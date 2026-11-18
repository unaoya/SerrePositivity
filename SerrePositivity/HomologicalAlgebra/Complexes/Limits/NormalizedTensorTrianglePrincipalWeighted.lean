module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorTrianglePrincipalActualCut
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorTrianglePrincipalOriginalCut
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.ConeTrianglePrincipalSign

/-!
概要：元の主切断の評価・単位合成と符号から、同じ中央相の全切断和を比較する。
方針：元の二つの切断・実評価成分・全添字と次数を保持する。
規約：全二次境界と混合 HA は別工程。使われ方：大域評価三角形の実三相単体。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.SSet
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.InfinityCategories
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (X Y : Complex A)

lemma normalizedTensorTriangle_principal_weighted_cut {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n)
    (τ : Fin (n + 1) →o Fin 3) (I : Finset (Fin (n + 1)))
    (hI : 2 ≤ I.card) (hc : 3 ≤ I.card)
    (hs1 : τ (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.second I hI) = 1)
    (hp1 : τ (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.penultimate I hI) = 1)
    (haz : τ (I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) = 0)
    (hbt : τ (I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) = 2)
    (k : ℤ) (hk : k = 2 - (I.card : ℤ)) (hJ : (I.filter (fun i => τ i = 1)).Nonempty)
    (hkJ : k + 1 = 1 - ((I.filter (fun i => τ i = 1)).card : ℤ)) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.penultimate I hI) •
      (_root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleData A X Y c τ).cutCompose I
        (I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) k
          (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.penultimate I hI))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.second I hI) •
        (_root_.SerrePositivity.ComplexLimits.normalizedTensorTrianglePinched A X Y c τ).toSimplexData.cutCompose I
          (I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) k
            (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.second I hI)) := by
  have ha := _root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleData_cutCompose_principal A X Y c τ I hI hc
    hs1 hp1 haz hbt k hk hJ hkJ
  have hb := _root_.SerrePositivity.ComplexLimits.normalizedTensorTrianglePinched_cutCompose_principal A X Y c τ I hI hc
    hs1 hp1 haz hbt k hk hJ hkJ
  have hx : (_root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleData A X Y c τ).obj (I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) = X := by
    change _root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleObj A X Y c τ _ = X
    simp only [_root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleObj, haz, ↓reduceIte]
  have hy : (_root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleData A X Y c τ).obj (I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) = Y := by
    change _root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleObj A X Y c τ _ = Y
    simp [_root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleObj, hbt]
  have hx' := _root_.SerrePositivity.ComplexLimits.normalizedTensorTrianglePinched_obj_ne_two A X Y c τ
    (I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (by rw [haz]; decide)
  have hy' : (_root_.SerrePositivity.ComplexLimits.normalizedTensorTrianglePinched A X Y c τ).obj (I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) = Y :=
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorTrianglePinched_obj_two A X Y c τ _ hbt).trans hy
  have heA := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.smul_sub_heq_of_obj_eq hx hy (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.penultimate I hI))
    _ 0 _ 0 ha (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_zero_heq hx hy rfl)
  have heB := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.smul_sub_heq_of_obj_eq hx' hy' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.second I hI))
    _ 0 _ 0 hb (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_zero_heq hx' hy' rfl)
  simp only [sub_zero] at heA heB
  rw [smul_smul, _root_.SerrePositivity.ComplexLimits.principal_cut_sign I hI (k + 1) (by omega)] at heA
  exact heA.trans heB.symm

end SerrePositivity.ComplexLimits
