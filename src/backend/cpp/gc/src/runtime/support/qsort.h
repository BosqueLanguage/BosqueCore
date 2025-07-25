#pragma once

#include <stdio.h>

//
//This quicksort implementation is designed to only work with addresses
//in a void**
//

void swap(void** arr, int first, int second) 
{
    void* tmp = arr[first];
    arr[first] = arr[second];
    arr[second] = tmp;
}

int partition(void** arr, int low, int high) 
{
    void* pi = arr[high];
    int i = low - 1;

    for(int j = low; j < high ; j++) {
        if(arr[j] < pi) {
            i++;
            swap(arr, i, j);
        }
    }
    swap(arr, i+1, high);
    return i + 1;
}

void qsort(void** arr, int low, int high, int size)
{
    if(low < high) {
        int pi = partition(arr, low, high);

        qsort(arr, low, pi - 1, size);
        qsort(arr, pi + 1, high, size);
    }
}