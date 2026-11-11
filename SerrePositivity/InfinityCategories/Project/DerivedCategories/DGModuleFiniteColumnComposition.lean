module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Algebra
public import SerrePositivity.DifferentialGraded.Module.Hom.ConeComparison
/-!
概要：有限個の閉包含を通る全次数係数の和を、微分と次の斉次合成について展開する。
方針：閉射による後合成の鎖写像性と、中間閉射を移す結合則を有限和へ適用する。
規約：元の全 Hom と実際の閉射を保持し、有限和の添字には宇宙変更を行わない。
使われ方：coherent bar の各列の微分と二乗項の展開。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {J : Type w} [Fintype J] {M T U : ModuleCategory R D} (N : J → ModuleCategory R D)
  (i : ∀ j, N j ⟶ T) (c : J → ℤˣ)

lemma dgModuleFiniteColumn_compose {p q n : ℤ}
    (f : ∀ j, (_root_.SerrePositivity.DifferentialGraded.moduleHom R D (ForgetEnrichment.to (Complex R) M)
      (ForgetEnrichment.to (Complex R) (N j))).X p)
    (g : (_root_.SerrePositivity.DifferentialGraded.moduleHom R D (ForgetEnrichment.to (Complex R) T)
      (ForgetEnrichment.to (Complex R) U)).X q) (h : p + q = n) :
    _root_.SerrePositivity.DifferentialGraded.compose R (x := ForgetEnrichment.to (Complex R) M)
      (y := ForgetEnrichment.to (Complex R) T) (z := ForgetEnrichment.to (Complex R) U)
      g (∑ j, c j • (eHomWhiskerLeft (Complex R) M (i j)).f p (f j)) h =
      ∑ j, c j • _root_.SerrePositivity.DifferentialGraded.compose R (x := ForgetEnrichment.to (Complex R) M)
        (y := ForgetEnrichment.to (Complex R) (N j)) (z := ForgetEnrichment.to (Complex R) U)
        ((eHomWhiskerRight (Complex R) (i j) U).f q g) (f j) h := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_sum_right (A := R) (D := _root_.SerrePositivity.DifferentialGraded.RightModule R D)
    (x := ForgetEnrichment.to (Complex R) M)
    (y := ForgetEnrichment.to (Complex R) T) (z := ForgetEnrichment.to (Complex R) U)]
  apply Finset.sum_congr rfl
  intro j _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_units_smul_right, moduleHomClosedInsertion R D
    (S := M) (M := N j) (N := T) (P := U)]

lemma dgModuleFiniteColumn_d {p : ℤ}
    (f : ∀ j, (_root_.SerrePositivity.DifferentialGraded.moduleHom R D (ForgetEnrichment.to (Complex R) M)
      (ForgetEnrichment.to (Complex R) (N j))).X p) :
    (_root_.SerrePositivity.DifferentialGraded.moduleHom R D (ForgetEnrichment.to (Complex R) M)
      (ForgetEnrichment.to (Complex R) T)).d p (p + 1)
      (∑ j, c j • (eHomWhiskerLeft (Complex R) M (i j)).f p (f j)) =
      ∑ j, c j • (eHomWhiskerLeft (Complex R) M (i j)).f (p + 1)
        ((moduleHom R D (ForgetEnrichment.to (Complex R) M)
          (ForgetEnrichment.to (Complex R) (N j))).d p (p + 1) (f j)) := by
  simp only [Units.smul_def, map_sum, map_zsmul]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  exact ConcreteCategory.congr_hom
    ((eHomWhiskerLeft (Complex R) M (i j)).comm p (p + 1)) (f j)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
