/*@
  requires 0 <= x < 100;
  assigns \nothing;
  ensures \result == x + 1;
*/
int add_one(int x)
{
  int result = x + 1;
  return result;
}
