; Since we don't have full support for SMT-LIB 3 scopes, this file defines
; the types for Ints and Reals and the bridge functions.  This makes those
; available in both theories without weird dependencies.

(declare-type Int ())
(declare-type Real ())

(declare-const to_int (-> Real Int))
(declare-const to_real (-> Int Real))
