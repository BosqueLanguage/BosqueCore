#pragma once

#include <stdio.h>

//
//This quicksort implementation is designed to only work with addresses
//in a void**
//

void swap(void** arr, int32_t first, int32_t second) 
{
    void* tmp = arr[first];
    arr[first] = arr[second];
    arr[second] = tmp;
}

int32_t partition(void** arr, int32_t low, int32_t high) 
{
    void* pi = arr[high];
    int32_t i = low - 1;

    for(int32_t j = low; j < high ; j++) {
        if(arr[j] < pi) {
            i++;
            swap(arr, i, j);
        }
    }
    swap(arr, i+1, high);
    return i + 1;
}

void __qsort(void** arr, int32_t low, int32_t high, int32_t size) noexcept 
{
    if(low < high) {
        int32_t pi = partition(arr, low, high);

        __qsort(arr, low, pi - 1, size);
        __qsort(arr, pi + 1, high, size);
    }   
}

void qsort(void** arr, int32_t low, int32_t high, int32_t size)
{
    if(high <= 0) {
        return ;
    }
    __qsort(arr, low, high, size);
}