#include <stdio.h>

class aclass {

    public:

    int x;

    aclass(void) { x = 42; }
    int  get_xa(void)    { return x; }
    int  get_my_x(void)  { return x; }
    int  get_the_x(void) { return get_my_x(); }

};

class bclass : public aclass {

    public:

    int x;

    bclass(void) { x = 99; }
    int  get_xb(void)    { return x; }
    int  get_my_x(void)  { return x; }
    // inherits get_the_x from parent aclass

};

int main()
{
    bclass b;

    printf("\nTesting field inheritance:\n");
    printf("x:get_xb = %d (using the method from bclass)\n", b.get_xb());
    printf("x:get_xa = %d (using the method from aclass)\n", b.get_xa());

    printf("\nTesting method inheritance:\n");
    printf("x:get_the_x  = %d\n",b.get_the_x());

}
