module
public import SerrePositivity.InfinityCategories.Derived.ContractingZeroVertex

/-! # 閉零圏の零対象から dg nerve の実零頂点へ

概要：閉零圏の零対象は零の収縮元を持ち、nerve の実零対象になる。
方針：恒等射と零射の一致を単位の次数零成分で評価する。
規約：h の零対象性とは区別する。使われ方：β3 の dg 加群圏の零対象。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 閉零圏の零対象では、dg 単位の実際の次数零成分は零。 -/
lemma dgUnitElement_eq_zero_of_closed_isZero (x : D)
    (hx : IsZero (ForgetEnrichment.of (Complex A) x)) : (unitElement A x).val = 0 := by
  have h := hx.eq_of_src (𝟙 (ForgetEnrichment.of (Complex A) x)) 0
  have hh := congrArg (fun f => (cycleFromUnit (homObject A D x x)
    (ForgetEnrichment.homTo (Complex A) f)).val) h
  change (unitElement A x).val = (cycleFromUnit (homObject A D x x) 0).val at hh
  change (unitElement A x).val = 0 at hh
  exact hh

/-- 閉零圏の零対象は実際の dg nerve の始対象かつ終対象。 -/
lemma dgNerve_isZeroVertex_of_closed_isZero (x : D)
    (hx : IsZero (ForgetEnrichment.of (Complex A) x)) :
    IsZeroVertex (X := dgNerve A D) (Simplex.vertex x) := by
  apply dgNerve_contractingElement_isZeroVertex x (0 : GradedHom A x x (-1))
  rw [map_zero, dgUnitElement_eq_zero_of_closed_isZero x hx]

end SerrePositivity.InfinityCategories
