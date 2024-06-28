include "buffer.dfy"
import opened Buffer

abstract module Scheduler {
  import opened Buffer
  method run_t(ibs: array<Buf>, obs: array<Buf>)
    requires ibs.Length >= 1
    requires obs.Length >= 1
    modifies ibs
    modifies obs
}
