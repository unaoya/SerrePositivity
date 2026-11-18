module
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorConeAugmentationAt
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorSelectedAugmentationVertex
public import SerrePositivity.EInfinity.Modules.ClosedPostcomposition

/-!
概要：元の cone の先端からの辺と同じ終端 augmentation の合成は元の恒等 cochain である。
方針：符号零次元と一点選択 cochain の恒等像を、実端点の輸送付きで使う。
規約：元の実辺を保つ。使われ方：二重 cone の三点方程式。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.HA.Section7_1_1
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.EInfinity.Modules _root_.SerrePositivity.ComplexLimits

open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open _root_.SerrePositivity.ComplexLimits.ConeHeadIndex
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorConeAugmentationAt_compose_mixed_pair {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : (0 : ℤ) = 2 - (I.card : ℤ)) (ha0 : a = 0) (h0 : 0 ∈ I) :
    HEq (compose A (closedHomEquiv A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X))) _ _ (strictRawModuleTensorConeAugmentationAt A X P Q c b)).val
      ((strictRawModuleTensorConeData A X P Q c).hom I a b 0 hI ha hb hk) (add_zero 0))
      (closedHomEquiv A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X))) _ _ (𝟙 ((strictRawModuleProbeFunctor A X).obj P))).val := by
  rw [modulePostcompose_graded]
  have hJ := _root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst_nonempty hI h0
  have hc : (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst I).card = 1 := by have := _root_.SerrePositivity.ComplexLimits.ConeHeadIndex.card_withoutFirst I h0; omega
  have hp := strictRawModuleTensorConeAugmentationAt_postcompose_mixed
    A X P Q c I a b 0 hI ha hb hk ha0 h0
  simp only [Int.negOnePow_zero, one_smul] at hp
  exact hp.trans (heq_of_eq
    (strictRawModuleTensorElementSelectedCochainAtMax_augmentation_vertex
      A X P Q c (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst I) hJ hc))

end SerrePositivity.EInfinity.BarrattEccles
