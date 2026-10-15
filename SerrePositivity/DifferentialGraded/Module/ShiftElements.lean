module
public import SerrePositivity.DifferentialGraded.Module.ShiftHom
public import SerrePositivity.DifferentialGraded.Module.HomElements

/-! # 全Homのshift射を斉次要素へ適用した成分と微分 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma moduleShiftHomElement_π (s : ℤ) {M N : RightModule A D} (q : ℤ)
    (z : (moduleHom A D M N).X q) (x : D) :
    (moduleHomπ A D (shiftModule s M) (shiftModule s N) x).f q
      ((moduleShiftHom A D s M N).f q z) =
        (s * q).negOnePow • ((moduleHomπ A D M N x).f q z).shift s := by
  have h := congrArg (fun f => f.f q z) (moduleShiftHom_π A D s M N x)
  change (moduleHomπ A D (shiftModule s M) (shiftModule s N) x).f q
    ((moduleShiftHom A D s M N).f q z) =
      (shiftHom s (M.obj (Opposite.op x)) (N.obj (Opposite.op x))).f q
        ((moduleHomπ A D M N x).f q z) at h
  exact h.trans (shiftHom_apply s _ _ q _)

lemma moduleShiftHomElement_d (s : ℤ) {M N : RightModule A D} (q r : ℤ)
    (z : (moduleHom A D M N).X q) :
    (moduleHom A D (shiftModule s M) (shiftModule s N)).d q r
      ((moduleShiftHom A D s M N).f q z) =
        (moduleShiftHom A D s M N).f r ((moduleHom A D M N).d q r z) :=
  congrArg (fun f => f z) ((moduleShiftHom A D s M N).comm q r)

end SerrePositivity.DifferentialGraded
