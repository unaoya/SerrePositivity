module
public import SerrePositivity.InfinityCategories.Derived.DGModuleShiftUnitNaturality
public import SerrePositivity.InfinityCategories.Derived.DGModuleRightShiftBoundaries
public import SerrePositivity.InfinityCategories.Derived.DGRepresentableDerivedPrimitives

/-! # 右シフト閉射と後合成の全次数の比較

概要：右シフト閉射の後合成を、元の全次数 Hom の後合成へ戻す。
方針：包含の自然性・結合則と Hom whiskering の斉次公式を使う。
規約：主導来零性は具体的な原始元から導く。使われ方：商の斉次境界性の比較写像への移送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerve.HomotopyComparison CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 閉加群射による Hom whiskering の斉次成分は通常順の後合成。 -/
lemma dgModulePostcompose_graded {L M N : ModuleCategory A D} (g : M ⟶ N) (n : ℤ)
    (f : GradedHom A (ForgetEnrichment.to (Complex A) L)
      (ForgetEnrichment.to (Complex A) M) n) :
    (eHomWhiskerLeft (Complex A) L g).f n f =
      compose A (closedHomEquiv A (RightModule A D) M N g).val f (add_zero n) := by
  have h := congrArg (fun l => l f) (Cochain.congr_v
    (modulePostcompositionMap_closed A D L g) n n (add_zero n))
  rw [modulePostcompositionMap_apply, Cochain.ofHom_v] at h
  exact h.symm

/-- shift 閉射を shift した閉射で後合成した cycle は、元の斉次後合成の右 shift。 -/
lemma dgModuleClosedRightShift_postcompose_cycle {L M N : ModuleCategory A D} (n : ℤ)
    (f : GradedHom A (ForgetEnrichment.to (Complex A) L)
      (ForgetEnrichment.to (Complex A) M) n) (hf : differential A f = 0) (g : M ⟶ N) :
    (closedHomEquiv A (RightModule A D) L (N⟦n⟧)
      (dgModuleClosedRightShift A D n f hf ≫ g⟦n⟧')).val =
      dgModuleHomRightShift A D n ((eHomWhiskerLeft (Complex A) L g).f n f) := by
  rw [closedHom_comp, dgModuleClosedRightShift_cycle, dgModulePostcompose_graded]
  unfold dgModuleHomRightShift
  rw [compose_assoc_of_sum _ _ _ (add_neg_cancel n) (add_zero (-n)) (zero_add 0),
    dgModuleShiftIn_naturality,
    ← compose_assoc_of_sum _ _ _ (add_zero n) (zero_add (-n)) (add_neg_cancel n)]
  rfl

/-- 元の後合成の原始元から、shift 閉射の後合成の主導来零性を得る。 -/
lemma dgModuleClosedRightShift_postcompose_zero_of_primitive {L M N : ModuleCategory A D}
    (hL : moduleHomotopicallyProjective A D L) (n k : ℤ) (hkn : k + 1 = n)
    (f : GradedHom A (ForgetEnrichment.to (Complex A) L)
      (ForgetEnrichment.to (Complex A) M) n) (hf : differential A f = 0) (g : M ⟶ N)
    (ha : ∃ a : (moduleHom A D (ForgetEnrichment.to (Complex A) L)
      (ForgetEnrichment.to (Complex A) N)).X k,
      (moduleHom A D (ForgetEnrichment.to (Complex A) L)
        (ForgetEnrichment.to (Complex A) N)).d k n a =
          (eHomWhiskerLeft (Complex A) L g).f n f) :
    (moduleToDerived A D).map (dgModuleClosedRightShift A D n f hf ≫ g⟦n⟧') = 0 := by
  apply (dgModuleProjectiveDerived_zero_iff_primitive A D hL _).mpr
  obtain ⟨a, ha⟩ := ha
  obtain ⟨h, hh⟩ := (dgModuleHomRightShift_exists_primitive_iff A D n k hkn
    ((eHomWhiskerLeft (Complex A) L g).f n f)).mpr ⟨a, ha⟩
  exact ⟨h, hh.trans (dgModuleClosedRightShift_postcompose_cycle A D n f hf g).symm⟩

end SerrePositivity.InfinityCategories
