-- Separate from audit_clmst_b3.lean: these compatibility statements intentionally
-- refer to the old finite-algebra choice and are relative to the old B-I input.
import SerrePositivity.CommutativeAlgebra.PerfectoidIdealCompatibility
import Mathlib.Util.PrintSorries

#print sorries SerrePositivity.exists_quotientPerfectoidization_equiv_finiteChoice
  SerrePositivity.perfectoidIdeal_eq_finiteChoice_kernel
