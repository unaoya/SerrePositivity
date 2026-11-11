module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniversalCommaCategory
/-!
概要：反対 dg 圏の同じ実閉前合成を、元の dg 圏の閉後合成へ戻す。
方針：閉射の向きと単位テンソルの交換を保持して豊穣合成を計算する。
規約：全整数次数を保持。使われ方：普遍余単位の comma の全 Hom 射影。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded MonoidalCategory BraidedCategory
variable (R : Type u) [CommRing R] (E : Type v) [DGCategory R E]
/-- 同じ実閉射の反対での前合成は、元の dg 圏での後合成。 -/
lemma dgOppositePrecomposition_eq_postcomposition {x y z : E}
    (s : ForgetEnrichment.of (Complex R) y ⟶ ForgetEnrichment.of (Complex R) z) :
    eHomWhiskerRight (Complex R)
      ((forgetEnrichmentOppositeEquivalence (Complex R) E).inverse.map s.op)
      (ForgetEnrichment.of (Complex R) (Opposite.op x)) =
    eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) x) s := by
  change (λ_ (homObject R E x y)).inv ≫
    (ForgetEnrichment.homTo (Complex R) s ⊗ₘ 𝟙 (homObject R E x y)) ≫
      eComp (Complex R) (Opposite.op z) (Opposite.op y) (Opposite.op x) =
    (ρ_ (homObject R E x y)).inv ≫
      (𝟙 (homObject R E x y) ⊗ₘ ForgetEnrichment.homTo (Complex R) s) ≫
        eComp (Complex R) x y z
  rw [tensorHom_eComp_op_eq, ← Category.assoc, leftUnitor_inv_braiding]
end SerrePositivity.InfinityCategories.Project.DerivedCategories
