#include <stdio.h>

void fused(unsigned n) 
{
    int a = 0;
    int b = 0;
    int c = 0;
    for (unsigned i = 0; i < n; i++) 
    {
        a++;
        b++;
	c++;
    }
}

void toBeFused(unsigned n) 
{
    int a = 0;
    int b = 0;
    int c = 0;
    for (unsigned i = 0; i < n; i++) 
    {
        a++;
    }
    for (unsigned i = 0; i < n; i++) 
    {
        b++;
	printf("text");
	//if (i) return;
    }
    unsigned m = n;
    c = -1;
    for (unsigned i = 0; i < m; i++) 
    {
        c++;
    }
}
