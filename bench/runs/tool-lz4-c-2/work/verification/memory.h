#include <stdint.h>

extern unsigned char mem[2097152];
extern uint32_t sb, se, db, de;

/*@ predicate readable(integer a, integer n) =
      0 <= n && ((sb <= a && a+n <= se) || (db <= a && a+n <= de));
    predicate writable(integer a, integer n) =
      0 <= n && db <= a && a+n <= de;
    predicate arena = 131072 <= sb <= se <= 2097152 &&
                      131072 <= db <= de <= 2097152 &&
                      (sb == se || db == de || se <= db || de <= sb);
*/

/*@ requires arena;
    requires readable(a, 1);
    assigns \nothing;
    ensures \result <= 255;
    ensures \result == mem[a];
*/
uint32_t load8(uint64_t a);

/*@ requires arena;
    requires readable(a, 2);
    assigns \nothing;
    ensures \result <= 65535;
*/
uint32_t load16(uint64_t a);

/*@ requires 65536 <= a <= 65596 && a % 4 == 0;
    assigns \nothing;
    ensures a == 65536 ==> \result == 0;
    ensures a == 65540 ==> \result == 1;
    ensures a == 65544 ==> \result == 2;
    ensures a == 65548 ==> \result == 1;
    ensures a == 65552 ==> \result == 0;
    ensures a == 65556 || a == 65560 || a == 65564 ==> \result == 4;
    ensures a == 65568 || a == 65572 || a == 65576 ==> \result == 0;
    ensures a == 65580 ==> \result == 4294967295;
    ensures a == 65584 ==> \result == 4294967292;
    ensures a == 65588 ==> \result == 1;
    ensures a == 65592 ==> \result == 2;
    ensures a == 65596 ==> \result == 3;
*/
uint32_t load32(uint64_t a);

/*@ requires arena;
    requires writable(a, 1);
    assigns mem[a];
*/
void store8(uint64_t a, uint32_t value);

/*@ requires arena;
    requires writable(a, 4);
    assigns mem[a .. a+3];
*/
void store32(uint64_t a, uint32_t value);
