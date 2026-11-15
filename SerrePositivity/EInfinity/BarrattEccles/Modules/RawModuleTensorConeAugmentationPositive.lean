module
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorConeAugmentationAt
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorSelectedAugmentation
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorConeOrdinaryZero
public import SerrePositivity.EInfinity.Modules.ClosedPostcomposition

/-!
概要：元の cone の全正次成分と同じ終端 augmentation の実合成は零である。
方針：通常成分は零、混合成分は同じ選択 cochain の augmentation 消滅へ戻す。
規約：元の実端点・符号・全有限集合を保つ。使われ方：二重 cone の高次方程式。
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
open SerrePositivity.EInfinity.Modules SerrePositivity.EInfinity.ComplexLimits

open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open ConeHeadIndex
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorConeAugmentationAt_compose_of_card_ge_three {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hc : 3 ≤ I.card) :
    compose A (closedHomEquiv A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X))) _ _ (strictRawModuleTensorConeAugmentationAt A X P Q c b)).val
      ((strictRawModuleTensorConeData A X P Q c).hom I a b k hI ha hb hk) (add_zero k) = 0 := by
  rw [modulePostcompose_graded]
  by_cases ha0 : a = 0
  · have h0 : (0 : Fin (n + 2)) ∈ I := by rw [← ha0, ha]; exact I.min'_mem _
    have hJ := withoutFirst_nonempty hI h0
    have hJtwo : 2 ≤ (withoutFirst I).card := by have := card_withoutFirst I h0; omega
    have hkJ : k = 1 - ((withoutFirst I).card : ℤ) := by
      have hs := card_withoutFirst I h0
      omega
    have hp := strictRawModuleTensorConeAugmentationAt_postcompose_mixed
      A X P Q c I a b k hI ha hb hk ha0 h0
    have hz := strictRawModuleTensorElementSelectedCochainAtMax_augmentation_smul_zero
      A X P Q c (withoutFirst I) k hJ hkJ hJtwo k.negOnePow
    have hx : (strictRawModuleTensorConeData A X P Q c).obj a = ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P) := by
      change strictRawModuleTensorConeObj A X P Q c a =
        ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P)
      rw [ha0, strictRawModuleTensorConeObj_zero]
    have hzero : HEq (0 : GradedHom A ((strictRawModuleTensorConeData A X P Q c).obj a) (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P)) k)
        (0 : GradedHom A (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P)) (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P)) k) := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_zero_heq hx rfl rfl
    exact eq_of_heq (hp.trans ((heq_of_eq hz).trans hzero.symm))
  · rw [strictRawModuleTensorConeData_hom_ordinary_zero A X P Q c I a b k hI ha hb hk ha0 (by omega)]
    exact map_zero _

end SerrePositivity.EInfinity.BarrattEccles
