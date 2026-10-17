module
public import SerrePositivity.DifferentialGraded.Verdier.ScalarKaroubiShift

/-! # Karoubi–Perf 正方形と非平坦係数変更の shift 整合性の公理監査 -/
@[expose] public section
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.DGQuotient
#print axioms natTransCommShift_of_precomp
#print axioms triaKaroubiPerfectFactorsCommShift
#print axioms triaKaroubiPerfectRestrictedSquareCommShift
#print axioms triaKaroubiPerfectSquareCommShift
#print axioms quotientScalarTriaPerfectSquareCommShift
#print axioms quotientScalarKaroubiPerfectSquareCommShift
#print axioms quotientScalarKaroubiPerfectSquareTriangle
