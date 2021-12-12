#include "config.h"
#include "types.h"
#include "debug.h"
#include "alloc-inl.h"
#include "utils.h"

#include <limits.h>
#include <math.h>
#include <assert.h>

// HorseFuzz: check whether a function belongs to (task) functions
int found(u32* fids, u32 id, u32 len) {
  int ret = -1;
  for (int i = 0; i < len; i++) {
    if (fids[i] == id)
      return i;
  }
  return ret;
}