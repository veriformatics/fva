/* GENERATED exact source prefix and export; see prepare.py. */
#include <stddef.h>
#include <stdint.h>
typedef uint8_t BYTE;
#define LZ4_FORCE_INLINE static
#define unlikely(x) ((x) != 0)
#define assert(condition) ((void)0)
#define DEBUGLOG(l, ...) {}
typedef enum { noDict = 0, withPrefix64k, usingExtDict, usingDictCtx } dict_directive;
typedef enum { decode_full_block = 0, partial_decode = 1 } earlyEnd_directive;
#define KB *(1 <<10)

/*@ requires count == 1 && p == begin;
    requires \valid_read(p);
    terminates \true;
    assigns \nothing;
    ensures \result == *p;
    exits \false;
*/
static BYTE entry_read(const BYTE *p, const BYTE *begin, int count) {
    return *p;
}

/*@ requires \false;
    terminates \false;
    exits \true;
*/
int omitted_decoder_tail(void);

/*@ requires src != \null && dst != \null;
    requires 0 <= srcSize <= 2097152;
    requires 0 <= outputSize <= 2097152;
    requires outputSize == 0 || srcSize == 0;
    requires partialDecoding == decode_full_block && dict == noDict;
    requires lowPrefix == (BYTE*)dst && dictStart == \null && dictSize == 0;
    requires \valid_read(src + (-32..srcSize-1));
    requires \valid(dst + (-32..outputSize-1));
    terminates \true;
    assigns \nothing;
    ensures \result == ((outputSize == 0 && srcSize == 1 && *(const BYTE*)src == 0)
                         ? 0 : -1);
    exits \false;
*/
LZ4_FORCE_INLINE int
LZ4_decompress_generic(
                 const char* const src,
                 char* const dst,
                 int srcSize,
                 int outputSize,         /* If endOnInput==endOnInputSize, this value is `dstCapacity` */

                 earlyEnd_directive partialDecoding,  /* full, partial */
                 dict_directive dict,                 /* noDict, withPrefix64k, usingExtDict */
                 const BYTE* const lowPrefix,  /* always <= dst, == dst when no prefix */
                 const BYTE* const dictStart,  /* only if dict==usingExtDict */
                 const size_t dictSize         /* note : = 0 if noDict */
                 )
{
    if ((src == NULL) || (outputSize < 0)) { return -1; }

    {   const BYTE* ip = (const BYTE*) src;
        const BYTE* const iend = ip + srcSize;

        BYTE* op = (BYTE*) dst;
        BYTE* const oend = op + outputSize;
        BYTE* cpy;

        const BYTE* const dictEnd = (dictStart == NULL) ? NULL : dictStart + dictSize;

        const int checkOffset = (dictSize < (int)(64 KB));


        /* Set up the "end" pointers for the shortcut. */
        const BYTE* const shortiend = iend - 14 /*maxLL*/ - 2 /*offset*/;
        const BYTE* const shortoend = oend - 14 /*maxLL*/ - 18 /*maxML*/;

        const BYTE* match;
        size_t offset;
        unsigned token;
        size_t length;


        DEBUGLOG(5, "LZ4_decompress_generic (srcSize:%i, dstSize:%i)", srcSize, outputSize);

        /* Special cases */
        assert(lowPrefix <= op);
        if (unlikely(outputSize==0)) {
            /* Empty output buffer */
            if (partialDecoding) return 0;
            return ((srcSize==1) && (entry_read(ip, (const BYTE*)src, srcSize)==0)) ? 0 : -1;
        }
        if (unlikely(srcSize==0)) { return -1; }

        return omitted_decoder_tail();
    }
}

int LZ4_decompress_safe(const char* source, char* dest, int compressedSize, int maxDecompressedSize)
{
    return LZ4_decompress_generic(source, dest, compressedSize, maxDecompressedSize,
                                  decode_full_block, noDict,
                                  (BYTE*)dest, NULL, 0);
}
