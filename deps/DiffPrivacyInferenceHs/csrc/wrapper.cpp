
#include <stdlib.h>
// #include <iostream>
#include "HsFFI.h"
#include "wrapper.h"
#include "Wrapper_stub.h"


void wrapperInit(void){
  // int argc = 2;
  // char *argv[] = { (char *)"+RTS", (char *)"-A32m", NULL };
  int argc = 0;
  char *argv[] = { NULL };
  char **pargv = argv;

  // Initialize Haskell runtime
  hs_init(&argc, &pargv);
}

void wrapperExit(void){
  hs_exit();
}



