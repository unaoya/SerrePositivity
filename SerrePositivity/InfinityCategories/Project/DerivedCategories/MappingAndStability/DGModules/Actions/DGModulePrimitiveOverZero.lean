module
public import SerrePositivity.DifferentialGraded.Derived.Projective
public import SerrePositivity.DifferentialGraded.Module.ConeConstruction
public import SerrePositivity.DifferentialGraded.Complexes.TensorCoproduct
/-!
概要：指定境界を後合成で零となる全 dg 自然な原始元へ持ち上げる。
方針：始域の K-projective 性と実 Hom 射の境界持ち上げを接続する。
規約：次数別全射性を明示する。使われ方：canonical cell 段の strict lift。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded HomologicalComplex
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
lemma dgModuleBoundary_primitive_over_zero
    (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
    {L M T N : ModuleCategory R D} (a : L ⟶ M) (b : M ⟶ T) (q : T ⟶ N)
    (hL : moduleHomotopicallyProjective R D L) (hq : moduleQuasiIso R D q)
    (hs : ∀ p : ℤ, Function.Surjective ((eHomWhiskerLeft (Complex R) L q).f p))
    (hz : a ≫ b ≫ q = 0) :
    ∃ h : (moduleHom R D (ForgetEnrichment.to (Complex R) L)
        (ForgetEnrichment.to (Complex R) T)).X (-1),
      (moduleHom R D (ForgetEnrichment.to (Complex R) L)
        (ForgetEnrichment.to (Complex R) T)).d (-1) 0 h =
          (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R)
            (C := RightModule R D) (X := L) (Y := T) (a ≫ b))).val ∧
        (eHomWhiskerLeft (Complex R) L q).f (-1) h = 0 := by
  let z := cycleFromUnit _ (ForgetEnrichment.homTo (Complex R)
            (C := RightModule R D) (X := L) (Y := T) (a ≫ b))
  let r := eHomWhiskerLeft (Complex R) L q
  have hr : QuasiIso r := moduleHomotopicallyProjective_postcompose_quasiIso R D hL q hq
  have hzero : r.f 0 z.val = 0 := by
    change (eHomWhiskerLeft (Complex R) L q).f 0
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R)
            (C := RightModule R D) (X := L) (Y := T) (a ≫ b))).val = 0
    rw [moduleHomCycle_postcompose, Category.assoc, hz]
    apply moduleHomElement_ext R D
    intro x
    rw [← moduleEvaluation_cochain, CategoryTheory.Functor.map_zero,
      CochainComplex.HomComplex.Cochain.ofHom_zero, map_zero]
  have hl := complex_boundary_lifting_of_surjective_quasiIso R r hs hr (-1)
  unfold complexBoundaryLiftAt at hl
  rw [show (-1 : ℤ) + 1 = 0 by decide] at hl
  exact hl z 0 (by simpa only [map_zero] using hzero)
end
end SerrePositivity.InfinityCategories.Project.DerivedCategories
