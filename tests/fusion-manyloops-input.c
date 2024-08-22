#include <stdio.h>

void toBeFused(int N, int M)
{
	for ( int i = 0; i < N; i++)
	{
		printf("Loop 1\n");
		for (int j = 0; j < M; j++)
		{
			printf("\tLoop 1.1\n");
		}
	}
	for (int k = 0; k < N; k++)
	{
		for (int l = 0; l < M; l++)
		{
			printf("\tLoop 2.1\n");
		}
		printf("Loop 2\n");
	}
}

void doit1(int *a, size_t n) {
    for (size_t i = 0; i < n; i++) {
        a[i] = a[i] + 3;
    }
    for (size_t i = 0; i < n; i++) {
        a[i] = a[i] * 5;
    }
    for (size_t i = 0; i < n; i++) {
        a[i] = a[i] - 23;
    }
    for (size_t i = 0; i < n; i++) {
        a[i] = (a[i] >> 10) & 0xFF;
    }
}

void doit2(int *a, size_t n) {
    for (size_t i = 0; i < n; i++) {
        a[i] = a[i] + 3;
        a[i] = a[i] * 5;
        a[i] = a[i] - 23;
        a[i] = (a[i] >> 10) & 0xFF;
    }
}

