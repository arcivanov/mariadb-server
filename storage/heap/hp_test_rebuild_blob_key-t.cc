/*
  Unit tests for HEAP blob key handling bugs.

  Bug A: rebuild_blob_key() has a heuristic (key_part->length ==
  field->pack_length()) that skips updating record[0], leaving stale data.

  Bug B: heap_prepare_hp_create_info() must override key_part->length
  for blob key parts from pack_length() to max_data_length().
  The DISTINCT key path sets key_part.length = pack_length() = 10,
  and the SQL layer's new_key_field() then creates Field_varstring(10),
  which truncates blob data.  heap_prepare_hp_create_info() must fix
  this by widening key_part->length to max_data_length() and updating
  store_length/key_length accordingly.
*/

#include <my_global.h>
#include <my_sys.h>
#include <m_string.h>
#include <tap.h>

#include "sql_priv.h"
#include "sql_class.h"  /* THD (full definition) */
#include "ha_heap.h"
#include "heapdef.h"

static const LEX_CSTRING test_field_name= {STRING_WITH_LEN("")};

/* Wrapper declared in ha_heap.cc under HEAP_UNIT_TESTS */
extern int test_heap_prepare_hp_create_info(TABLE *table_arg,
                                            bool internal_table,
                                            HP_CREATE_INFO *hp_create_info);

/*
  Record layout for test table (nullable tinyblob(16)):
    byte 0:     null bitmap (bit 2 = blob null)
    bytes 1-2:  blob packlength=2 (length, little-endian)
    bytes 3-10: blob data pointer (8 bytes)
  reclength = 11
*/
#define T_REC_NULL_OFFSET  0
#define T_REC_BLOB_OFFSET  1
#define T_REC_BLOB_PACKLEN 2
#define T_REC_LENGTH       11


/*
  Helper: create a Field_blob using the full server constructor
  (the same one make_table_field uses) via placement new.
  Sets field_length = BLOB_PACK_LENGTH_TO_MAX_LENGH(packlength),
  matching real server behavior.
*/
static Field_blob *
make_test_field_blob(void *storage, uchar *ptr, uchar *null_ptr,
                     uchar null_bit, TABLE_SHARE *share,
                     uint packlength, CHARSET_INFO *cs)
{
  static const LEX_CSTRING fname= {STRING_WITH_LEN("")};
  return ::new (storage) Field_blob(ptr, null_ptr, null_bit,
                                    Field::NONE, &fname,
                                    share, packlength,
                                    DTCollation(cs));
}


class Hp_test_rebuild_blob_key
{
  alignas(ha_heap) char h_storage[sizeof(ha_heap)];
  ha_heap *h;
  HP_INFO  hp_info;
  TABLE    tbl;
  TABLE_SHARE tbl_share;
  uchar    rec_buf[T_REC_LENGTH];
  uchar    lastkey_buf[64];

  HA_KEYSEG seg;
  HP_KEYDEF keydef;

  /* SQL-layer key info needed by rebuild_blob_key's Bug A heuristic */
  KEY_PART_INFO kpi;
  KEY sql_key;
  /* Stack-allocated to avoid Field::operator new which needs THD */
  alignas(Field_blob) char blob_storage[sizeof(Field_blob)];
  Field_blob *blob_field;

public:
  Hp_test_rebuild_blob_key()
  {
    memset(h_storage, 0, sizeof(h_storage));
    h= reinterpret_cast<ha_heap*>(h_storage);

    memset(&hp_info, 0, sizeof(hp_info));
    hp_info.lastkey= lastkey_buf;
    h->file= &hp_info;

    /* TABLE_SHARE needed by Field_blob constructor (blob_fields++) */
    memset(static_cast<void*>(&tbl_share), 0, sizeof(tbl_share));

    /* Set up blob keyseg */
    memset(&seg, 0, sizeof(seg));
    seg.type=      HA_KEYTYPE_VARTEXT1;
    seg.flag=      HA_BLOB_PART | HA_VAR_LENGTH_PART;
    seg.start=     T_REC_BLOB_OFFSET;
    seg.length=    0;
    seg.bit_start= T_REC_BLOB_PACKLEN;
    seg.charset=   &my_charset_bin;
    seg.null_bit=  2;
    seg.null_pos=  T_REC_NULL_OFFSET;

    memset(&keydef, 0, sizeof(keydef));
    keydef.keysegs=    1;
    keydef.seg=        &seg;
    keydef.algorithm=  HA_KEY_ALG_HASH;
    keydef.length=     1 + 4 + (uint) sizeof(void*);
    keydef.has_blob_seg= 1;

    /*
      Set up Field_blob using the full server constructor — same one
      that make_table_field() uses.  This sets field_length to
      BLOB_PACK_LENGTH_TO_MAX_LENGH(packlength), matching real behavior.
    */
    blob_field= make_test_field_blob(blob_storage,
                                     rec_buf + T_REC_BLOB_OFFSET,
                                     rec_buf + T_REC_NULL_OFFSET,
                                     2, &tbl_share,
                                     T_REC_BLOB_PACKLEN,
                                     &my_charset_bin);

    memset(&kpi, 0, sizeof(kpi));
    kpi.field= blob_field;
    kpi.offset= T_REC_BLOB_OFFSET;
    /* DISTINCT path sets length = pack_length() — this triggers Bug A */
    kpi.length= (uint16) blob_field->pack_length();
    kpi.key_part_flag= blob_field->key_part_flag();

    memset(&sql_key, 0, sizeof(sql_key));
    sql_key.user_defined_key_parts= 1;
    sql_key.usable_key_parts= 1;
    sql_key.key_part= &kpi;
    sql_key.algorithm= HA_KEY_ALG_HASH;

    /* Set up TABLE */
    memset(static_cast<void*>(&tbl), 0, sizeof(tbl));
    tbl.record[0]= rec_buf;
    tbl.key_info= &sql_key;
    tbl.s= &tbl_share;
    h->table= &tbl;

    blob_field->table= &tbl;
  }

  ~Hp_test_rebuild_blob_key()
  {
    blob_field->~Field_blob();
  }

  static uint build_varstring_key(uchar *dst, const uchar *data, uint16 len)
  {
    uchar *p= dst;
    *p++= 0;  /* not null */
    int2store(p, len);
    p+= 2;
    memcpy(p, data, len);
    p+= len;
    return (uint)(p - dst);
  }

  ulong hash_record(const uchar *data, uint16 len)
  {
    uchar rec[T_REC_LENGTH];
    memset(rec, 0, sizeof(rec));
    int2store(rec + T_REC_BLOB_OFFSET, len);
    memcpy(rec + T_REC_BLOB_OFFSET + T_REC_BLOB_PACKLEN,
           &data, sizeof(void*));
    return hp_rec_hashnr(&keydef, rec);
  }

  /*
    Bug A: rebuild_blob_key must overwrite record[0] from the key.

    key_part->length == field->pack_length() == 10, which triggers
    the buggy heuristic.  With stale data in record[0], the rebuilt
    hash will match the stale data instead of the correct data.

    Test FAILS when the heuristic is present.
  */
  void test_bug_a()
  {
    const uchar *correct_data= (const uchar*) "1 - 00xxxxxxxxxx";
    uint16 correct_len= 16;
    const uchar *stale_data= (const uchar*) "1 - 03xxxxxxxxxx";
    uint16 stale_len= 16;

    ulong correct_hash= hash_record(correct_data, correct_len);
    ulong stale_hash= hash_record(stale_data, stale_len);

    ok(correct_hash != stale_hash,
       "Bug A setup: correct hash != stale hash");

    /* Pre-populate record[0] with STALE data */
    memset(rec_buf, 0, T_REC_LENGTH);
    int2store(rec_buf + T_REC_BLOB_OFFSET, stale_len);
    memcpy(rec_buf + T_REC_BLOB_OFFSET + T_REC_BLOB_PACKLEN,
           &stale_data, sizeof(void*));

    /* Build varstring key with CORRECT data */
    uchar vkey[64];
    build_varstring_key(vkey, correct_data, correct_len);

    /* Call rebuild_blob_key (active_key_index=0) */
    const uchar *rebuilt;
    h->rebuild_blob_key(&keydef, vkey, 0, &rebuilt);

    /* Hash record[0] after rebuild */
    ulong rebuilt_hash= hp_rec_hashnr(&keydef, rec_buf);

    ok(rebuilt_hash == correct_hash,
       "Bug A: rebuilt hash (%lu) == correct hash (%lu)",
       rebuilt_hash, correct_hash);
    ok(rebuilt_hash != stale_hash,
       "Bug A: rebuilt hash (%lu) != stale hash (%lu)",
       rebuilt_hash, stale_hash);
  }

  /*
    Bug B: heap_prepare_hp_create_info must override key_part->length
    for blob key parts from pack_length() to max_data_length().

    The DISTINCT key path sets key_part.length = pack_length() = 10.
    The SQL layer's new_key_field() then creates Field_varstring(10),
    which truncates blob data longer than 10 bytes.

    heap_prepare_hp_create_info must widen key_part->length to
    max_data_length() (the maximum data the blob type can hold)
    and update store_length/key_length accordingly, so that
    new_key_field() creates a Field_varstring large enough for
    the full blob data.

    FAILS when the override is missing (key_part.length stays at 10).
    PASSES when heap_prepare_hp_create_info overrides to max_data_length().
  */
  void test_bug_b()
  {
    uchar local_rec[T_REC_LENGTH];
    memset(local_rec, 0, sizeof(local_rec));

    TABLE_SHARE share;
    memset(static_cast<void*>(&share), 0, sizeof(share));
    share.fields= 1;
    share.blob_fields= 0;  /* Field_blob constructor increments this */
    share.keys= 1;
    share.reclength= T_REC_LENGTH;
    share.rec_buff_length= T_REC_LENGTH;
    share.db_record_offset= 1;

    alignas(Field_blob) char bf_storage[sizeof(Field_blob)];
    Field_blob *bfp= make_test_field_blob(bf_storage,
                                          local_rec + T_REC_BLOB_OFFSET,
                                          local_rec + T_REC_NULL_OFFSET,
                                          2, &share,
                                          T_REC_BLOB_PACKLEN,
                                          &my_charset_bin);
    Field_blob &bf= *bfp;
    bf.field_index= 0;

    Field *field_array[2]= { &bf, NULL };

    KEY_PART_INFO local_kpi;
    memset(&local_kpi, 0, sizeof(local_kpi));
    local_kpi.field= &bf;
    local_kpi.offset= T_REC_BLOB_OFFSET;
    local_kpi.length= (uint16) bf.pack_length();  /* = 10 (the bug) */
    local_kpi.key_part_flag= bf.key_part_flag();
    local_kpi.type= bf.key_type();

    KEY local_sql_key;
    memset(&local_sql_key, 0, sizeof(local_sql_key));
    local_sql_key.user_defined_key_parts= 1;
    local_sql_key.usable_key_parts= 1;
    local_sql_key.key_part= &local_kpi;
    local_sql_key.algorithm= HA_KEY_ALG_HASH;

    TABLE test_table;
    memset(static_cast<void*>(&test_table), 0, sizeof(test_table));
    test_table.record[0]= local_rec;
    test_table.s= &share;
    test_table.field= field_array;
    test_table.key_info= &local_sql_key;
    share.key_info= &local_sql_key;

    bf.table= &test_table;

    uint blob_offsets[1]= { 0 };
    share.blob_field= blob_offsets;

    /*
      Simulate DISTINCT key path: set store_length and key_length
      based on key_part.length = pack_length() = 10, same as finalize().
    */
    local_kpi.store_length= local_kpi.length;
    if (bf.real_maybe_null())
      local_kpi.store_length+= HA_KEY_NULL_LENGTH;
    local_kpi.store_length+= bf.key_part_length_bytes();
    local_sql_key.key_length= local_kpi.store_length;

    ok(local_kpi.length == bf.pack_length(),
       "Bug B setup: key_part.length = pack_length() = %u",
       (uint) local_kpi.length);

    /*
      heap_prepare_hp_create_info accesses current_thd for
      max_heap_table_size.  Provide a zero-initialized THD.
    */
    char *fake_thd= (char*) calloc(1, sizeof(THD));
    THD *real_thd= (THD*) fake_thd;
    real_thd->variables.max_heap_table_size= 1024*1024;
    set_current_thd(real_thd);

    HP_CREATE_INFO hp_ci;
    memset(&hp_ci, 0, sizeof(hp_ci));
    hp_ci.max_table_size= 1024*1024;
    hp_ci.keys= 1;
    hp_ci.reclength= T_REC_LENGTH;

    int err= test_heap_prepare_hp_create_info(&test_table, TRUE, &hp_ci);

    set_current_thd(NULL);
    free(fake_thd);

    ok(err == 0,
       "Bug B: heap_prepare_hp_create_info succeeded (err=%d)", err);

    /*
      After fix: key_part.length must equal max_data_length() for the
      blob's packlength.  For packlength=2 this is 65535.  This ensures
      the SQL layer's new_key_field() creates a Field_varstring large
      enough to hold the full blob data without truncation.
    */
    uint32 expected_length= bf.max_data_length();
    ok(local_kpi.length == expected_length,
       "Bug B: key_part.length (%u) == max_data_length() (%u)",
       (uint) local_kpi.length, (uint) expected_length);

    /*
      store_length and key_length must be updated consistently:
      the delta from widening key_part.length must propagate to both.
    */
    uint expected_store_length= expected_length;
    if (bf.real_maybe_null())
      expected_store_length+= HA_KEY_NULL_LENGTH;
    expected_store_length+= bf.key_part_length_bytes();
    ok(local_kpi.store_length == expected_store_length,
       "Bug B: store_length (%u) == expected (%u)",
       (uint) local_kpi.store_length, (uint) expected_store_length);
    ok(local_sql_key.key_length == expected_store_length,
       "Bug B: key_length (%u) == expected (%u)",
       (uint) local_sql_key.key_length, (uint) expected_store_length);

    my_free(hp_ci.keydef);
    my_free(hp_ci.blob_descs);
  }
};


/*
  Bug 7/8: heap_prepare_hp_create_info uses key_part->key_part_flag to
  decide whether a key segment is a blob.  Several SQL layer paths
  (SJ weedout, expression cache) leave key_part_flag uninitialized.
  If the garbage value has HA_BLOB_PART set, heap_prepare_hp_create_info
  zeroes seg->length and treats the segment as a blob, corrupting the
  HEAP hash index for non-blob VARCHAR/VARBINARY keys.

  Bug 7 manifests as row loss in SJ lookups (HA_ERR_KEY_NOT_FOUND on
  non-blob keys).  Bug 8 manifests as COUNT(*)=1 instead of thousands
  because every insert after the first is rejected as a duplicate.

  Test: create a TABLE with a non-blob Field_varstring key and set
  key_part_flag to garbage containing HA_BLOB_PART.  Call
  test_heap_prepare_hp_create_info and verify the resulting HEAP key
  segment has the correct length (not 0) and does not have HA_BLOB_PART.
*/

/*
  Record layout for varchar test table (non-nullable varbinary(28)):
    byte 0:     null bitmap (all zero for NOT NULL)
    byte 1:     varchar length_bytes=1 (field_length=28 < 256)
    bytes 2-29: varchar data (28 bytes max)
  reclength = 30
*/
#define V_REC_NULL_OFFSET  0
#define V_REC_VARCHAR_OFFSET 1
#define V_REC_VARCHAR_LEN  28
#define V_REC_LENGTH       30


class Hp_test_varchar_key_flag
{
  alignas(Field_varstring) char vs_storage[sizeof(Field_varstring)];
  Field_varstring *vs_field;
  TABLE_SHARE share;
  TABLE test_table;
  uchar rec_buf[V_REC_LENGTH];
  KEY_PART_INFO local_kpi;
  KEY local_sql_key;

public:
  Hp_test_varchar_key_flag()
  {
    memset(rec_buf, 0, sizeof(rec_buf));
    memset(static_cast<void*>(&share), 0, sizeof(share));
    share.fields= 1;
    share.keys= 1;
    share.reclength= V_REC_LENGTH;
    share.rec_buff_length= V_REC_LENGTH;
    share.db_record_offset= 1;

    static const LEX_CSTRING fname= {STRING_WITH_LEN("")};
    vs_field= ::new (vs_storage) Field_varstring(
        rec_buf + V_REC_VARCHAR_OFFSET,
        V_REC_VARCHAR_LEN,
        1,           /* length_bytes: 1 for field_length < 256 */
        (uchar*) 0,  /* null_ptr: NOT NULL */
        0,            /* null_bit */
        Field::NONE,
        &fname,
        &share,
        DTCollation(&my_charset_bin));

    vs_field->field_index= 0;

    Field *field_array[2]= { vs_field, NULL };

    /*
      Simulate SJ weedout: leave key_part_flag UNINITIALIZED.
      We set it to garbage containing HA_BLOB_PART to reproduce
      the exact failure condition.
    */
    memset(&local_kpi, 0, sizeof(local_kpi));
    local_kpi.field= vs_field;
    local_kpi.offset= V_REC_VARCHAR_OFFSET;
    local_kpi.length= (uint16) vs_field->key_length();
    local_kpi.type= vs_field->key_type();
    /* Poison key_part_flag with garbage including HA_BLOB_PART (0x20) */
    local_kpi.key_part_flag= 0xA5A5;  /* garbage from uninitialized memory */

    memset(&local_sql_key, 0, sizeof(local_sql_key));
    local_sql_key.user_defined_key_parts= 1;
    local_sql_key.usable_key_parts= 1;
    local_sql_key.key_part= &local_kpi;
    local_sql_key.algorithm= HA_KEY_ALG_HASH;
    local_sql_key.key_length= local_kpi.length + 2; /* + varchar pack len */

    memset(static_cast<void*>(&test_table), 0, sizeof(test_table));
    test_table.record[0]= rec_buf;
    test_table.s= &share;
    test_table.field= field_array;
    test_table.key_info= &local_sql_key;
    share.key_info= &local_sql_key;

    vs_field->table= &test_table;

    /* No blob fields */
    uint blob_offsets[1]= { 0 };
    share.blob_field= blob_offsets;
    share.blob_fields= 0;
  }

  ~Hp_test_varchar_key_flag()
  {
    vs_field->~Field_varstring();
  }

  void test_bug_7_8()
  {
    /* Verify setup: key_part_flag has HA_BLOB_PART set (the poison) */
    ok((local_kpi.key_part_flag & HA_BLOB_PART) != 0,
       "Bug 7/8 setup: key_part_flag has HA_BLOB_PART set (garbage)");
    ok(local_kpi.length == V_REC_VARCHAR_LEN,
       "Bug 7/8 setup: key_part.length = %u (field_length)",
       (uint) local_kpi.length);

    char *fake_thd= (char*) calloc(1, sizeof(THD));
    THD *real_thd= (THD*) fake_thd;
    real_thd->variables.max_heap_table_size= 1024*1024;
    set_current_thd(real_thd);

    HP_CREATE_INFO hp_ci;
    memset(&hp_ci, 0, sizeof(hp_ci));
    hp_ci.max_table_size= 1024*1024;
    hp_ci.keys= 1;
    hp_ci.reclength= V_REC_LENGTH;

    int err= test_heap_prepare_hp_create_info(&test_table, TRUE, &hp_ci);

    set_current_thd(NULL);
    free(fake_thd);

    ok(err == 0,
       "Bug 7/8: heap_prepare_hp_create_info succeeded (err=%d)", err);

    /*
      After heap_prepare_hp_create_info + hp_create processing:
      - seg->length must be V_REC_VARCHAR_LEN (28), NOT 0
      - seg->flag must NOT have HA_BLOB_PART (it's a plain varchar)
      - keydef->length must include 2 (varchar pack) + seg->length
    */
    HA_KEYSEG *seg= hp_ci.keydef[0].seg;
    ok(seg->length == V_REC_VARCHAR_LEN,
       "Bug 7/8: seg->length = %u (expected %u, NOT 0)",
       (uint) seg->length, (uint) V_REC_VARCHAR_LEN);

    ok(!(seg->flag & HA_BLOB_PART),
       "Bug 7/8: seg->flag (0x%x) does NOT have HA_BLOB_PART",
       (uint) seg->flag);

    /*
      Functional test: verify that hp_rec_hashnr produces different
      hashes for different varchar values.  The write path uses
      hp_rec_hashnr for duplicate detection (hp_write_key line 406/443).
      If seg->length=0, all records hash identically — every insert
      after the first is a false "duplicate" (Bug 8: COUNT(*)=1).
    */
    HP_KEYDEF *kd= &hp_ci.keydef[0];

    /*
      hp_make_key must produce different key buffers for different values.
      If seg->length=0, hp_make_key writes only the 2-byte prefix with
      no data, so all keys are identical regardless of varchar content.
    */
    {
      uchar mk1[64], mk2[64];
      memset(mk1, 0, sizeof(mk1));
      memset(mk2, 0, sizeof(mk2));
      uchar mr1[V_REC_LENGTH], mr2[V_REC_LENGTH];
      memset(mr1, 0, sizeof(mr1));
      mr1[V_REC_VARCHAR_OFFSET]= 4;
      memcpy(mr1 + V_REC_VARCHAR_OFFSET + 1, "XXXX", 4);
      memset(mr2, 0, sizeof(mr2));
      mr2[V_REC_VARCHAR_OFFSET]= 4;
      memcpy(mr2 + V_REC_VARCHAR_OFFSET + 1, "YYYY", 4);
      hp_make_key(kd, mk1, mr1);
      hp_make_key(kd, mk2, mr2);
      /*
        Expected key length: 2 (varchar pack) + seg->length bytes of data.
        Use V_REC_VARCHAR_LEN (the correct seg->length) so the comparison
        covers actual data bytes, not just the 2-byte prefix.
      */
      ok(memcmp(mk1, mk2, 2 + V_REC_VARCHAR_LEN) != 0,
         "Bug 7/8: hp_make_key produces different keys for different values");
    }

    /* Record 1: "AAAA" */
    uchar r1[V_REC_LENGTH];
    memset(r1, 0, sizeof(r1));
    r1[V_REC_VARCHAR_OFFSET]= 4;  /* length=4, 1-byte prefix */
    memcpy(r1 + V_REC_VARCHAR_OFFSET + 1, "AAAA", 4);

    /* Record 2: "BBBB" */
    uchar r2[V_REC_LENGTH];
    memset(r2, 0, sizeof(r2));
    r2[V_REC_VARCHAR_OFFSET]= 4;
    memcpy(r2 + V_REC_VARCHAR_OFFSET + 1, "BBBB", 4);

    ulong rh1= hp_rec_hashnr(kd, r1);
    ulong rh2= hp_rec_hashnr(kd, r2);

    ok(rh1 != rh2,
       "Bug 8: different records produce different rec hashes "
       "(rh1=%lu, rh2=%lu)", rh1, rh2);

    /*
      Also verify hp_rec_key_cmp reports them as different.
      If seg->length=0, the comparison may also break.
    */
    ok(hp_rec_key_cmp(kd, r1, r2, NULL) != 0,
       "Bug 7: different records compare as different");

    my_free(hp_ci.keydef);
  }
};


int main(int argc __attribute__((unused)),
         char **argv __attribute__((unused)))
{
  MY_INIT("hp_test_rebuild_blob_key");
  /* Field constructors reference system_charset_info via DTCollation */
  system_charset_info= &my_charset_latin1;
  plan(16);

  Hp_test_rebuild_blob_key t;

  diag("Bug A: stale record[0] in rebuild_blob_key");
  t.test_bug_a();

  diag("Bug B: key_part->length override for blob key parts");
  t.test_bug_b();

  diag("Bug 7/8: uninitialized key_part_flag corrupts non-blob varchar keys");
  Hp_test_varchar_key_flag t2;
  t2.test_bug_7_8();

  my_end(0);
  return exit_status();
}
