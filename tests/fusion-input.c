#include <stdlib.h>

void fused() 
{
    int a = 0;
    int b = 0;
    for (size_t i = 0; i < 228; i++) 
    {
        a++;
        b++;
    }
}

void toBeFused() 
{
    int a = 0;
    int b = 0;
    for (size_t i = 0; i < 228; i++) 
    {
        a++;
    }
    for (size_t i = 0; i < 228; i++) 
    {
        b++;
    }

}
