#pragma once

#include "./flagmgr.h"

/**
 * This file contains the flags that are used to enable and disable various features and diagnostics in the runtime. 
 * GC specific performance flags (nursery size etc.) are in the allocator/flags.h file. 
 **/

#ifdef BSQ_POSTREE_VALIDATE
    REGISTER_DIAGNOSTIC_FLAG(BSQ_POSTREE_VALIDATE, "true", "Enable/Disable postree validation checks", "false")
#else
    REGISTER_DIAGNOSTIC_FLAG(BSQ_POSTREE_VALIDATE, "false", "Enable/Disable postree validation checks", "false")
#endif

////
//ENABLE DIAGNOSTICS
//#define BSQ_POSTREE_VALIDATE 1
#define GC_METRICS_BASIC 0
////