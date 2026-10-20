module
public import SerrePositivity.InfinityCategories.Derived.DGClosedPostcompositionChainMap
public import SerrePositivity.InfinityCategories.Derived.DGModuleUnitPostcomposition
public import SerrePositivity.InfinityCategories.Derived.DGClosedHomWhiskerNaturality
/-!
概要：R の代表加群からの全 Hom 後合成を、対象宇宙の持ち上げの前後で厳密に照合する。
方針：同じ実 dg 関手の Hom 自然性と、その恒等 Hom 写像を使う。
規約：準同型は全次数で保つ。使われ方：基礎空間関手による実準同型の反転。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
variable (R : Type u) [CommRing R] (D : Type v)
/-- 同じ対象宇宙の持ち上げは、R からの全 Hom 後合成そのものを変えない。 -/
lemma dgHomModuleUnitPostcomp_lift {M N : RightModule R PUnit.{1}}
    (f : ForgetEnrichment.of (Complex R) M ⟶ ForgetEnrichment.of (Complex R) N) :
    dgClosedPostcomposition R
      (DGUniverseLift.{u + 1, max (u + 1) v} (RightModule R PUnit.{1}))
      (x := dgHomModuleUnit R D)
      ((dgUniverseLiftUp.{u, u + 1, max (u + 1) v} R (RightModule R PUnit.{1})).onClosed.map f) =
      eHomWhiskerLeft (Complex R)
        (ForgetEnrichment.of (Complex R) (representable R PUnit.unit)) f := by
  have h := dgFunctorHom_postcompose
    (dgUniverseLiftUp.{u, u + 1, max (u + 1) v} R (RightModule R PUnit.{1}))
    (ForgetEnrichment.of (Complex R) (representable R PUnit.unit)) f
  simp only [dgUniverseLiftUp, Category.comp_id, Category.id_comp] at h
  exact h.symm
/-- 元の加群の準同型は、持ち上げた同じ R からの全 Hom 後合成でも準同型。 -/
lemma dgHomModuleUnitPostcomp_lift_quasiIso {M N : RightModule R PUnit.{1}}
    (f : ForgetEnrichment.of (Complex R) M ⟶ ForgetEnrichment.of (Complex R) N)
    (hf : moduleQuasiIso R PUnit.{1} f) :
    QuasiIso (dgClosedPostcomposition R
      (DGUniverseLift.{u + 1, max (u + 1) v} (RightModule R PUnit.{1}))
      (x := dgHomModuleUnit R D)
      ((dgUniverseLiftUp.{u, u + 1, max (u + 1) v} R
        (RightModule R PUnit.{1})).onClosed.map f)) := by
  rw [dgHomModuleUnitPostcomp_lift]
  exact moduleHomotopicallyProjective_postcompose_quasiIso R PUnit.{1}
    (representable_homotopicallyProjective R PUnit.{1} PUnit.unit) f hf
end SerrePositivity.InfinityCategories
