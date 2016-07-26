#include <stdio.h>
#include <stdlib.h>

typedef struct frac_t
{
  int num;
  int div;
} frac_t;

//! frac constructor
frac_t frac(int num, int div);

//! frac addition
frac_t add(frac_t a, frac_t b);

//! greatest common divisor
int gcd(int a, int b);

// ---

int main(/*int argc; char** argv*/)
{
  const frac_t a = frac(1, 2);
  const frac_t b = frac(1, 3);
  const frac_t ab = add(a, b);
  printf("%d/%d + %d/%d = %d/%d\n", a.num, a.div,  b.num, b.div,  ab.num, ab.div);

  return 0;
}

// ---

/**
 */
frac_t frac(int num, int div)
{
  frac_t ret = { num, div };

  if(ret.num == 0)
    ret.div = 1;

  if(ret.div == 1)
    return ret;

  const int nd_gcd = gcd(ret.num, ret.div);
  ret.num /= nd_gcd;
  ret.div /= nd_gcd;

  return ret;
}

/**
 * TODO: least common multiple is missing.
 *
 * This is prone to overflows!
 */
frac_t add(const frac_t a, const frac_t b)
{
  return frac(a.num*b.div + b.num*a.div, a.div * b.div);
}

// ---

/**
 */
int gcd(int a, int b)
{
  if(a == 0)
    return b;

  a = abs(a);
  b = abs(b);

  while(b != 0)
  {
    const int t = b;
    b = a % b;
    a = t;
  }

  return a;
}

