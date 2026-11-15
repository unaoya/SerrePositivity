module
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorConeComponents
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorElementDiagram
public import SerrePositivity.EInfinity.Modules.ClosedPostcomposition

/-!
概要：元の実 cone の各対象から同じ先端 X への augmentation と混合成分の像を構成する。
方針：先端では恒等、通常対象では同じ frame augmentation を使い、端点輸送を保持する。
規約：元の実対象・射・符号を保つ。使われ方：大域 augmentation 三角形の二重 cone。
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
open SerrePositivity.InfinityCategories.HA.Section7_1_1
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.EInfinity.Modules SerrePositivity.EInfinity.ComplexLimits
open scoped Simplicial
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

def strictRawModuleTensorConeAugmentationAt {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) (i : Fin (n + 2)) :
    ForgetEnrichment.of (Complex A) ((strictRawModuleTensorConeData A X P Q c).obj i) ⟶ ((strictRawModuleProbeFunctor A X).obj P) := by
  induction i using Fin.cases with
  | zero => exact 𝟙 ((strictRawModuleProbeFunctor A X).obj P)
  | succ i => exact (strictRawModuleTensorElementAugmentation A X P Q).app (c.obj i)

lemma strictRawModuleTensorConeAugmentationAt_zero {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    strictRawModuleTensorConeAugmentationAt A X P Q c 0 = 𝟙 ((strictRawModuleProbeFunctor A X).obj P) := rfl

lemma strictRawModuleTensorConeAugmentationAt_succ {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) (i : Fin (n + 1)) :
    strictRawModuleTensorConeAugmentationAt A X P Q c i.succ =
      (strictRawModuleTensorElementAugmentation A X P Q).app (c.obj i) := rfl

lemma strictRawModuleTensorConeAugmentationAt_postcompose_mixed {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (ha0 : a = 0) (h0 : 0 ∈ I) :
    HEq ((eHomWhiskerLeft (Complex A) (ForgetEnrichment.of (Complex A) ((strictRawModuleTensorConeData A X P Q c).obj a))
      (strictRawModuleTensorConeAugmentationAt A X P Q c b)).f k
        ((strictRawModuleTensorConeData A X P Q c).hom I a b k hI ha hb hk))
      ((eHomWhiskerLeft (Complex A) ((strictRawModuleProbeFunctor A X).obj P) ((strictRawModuleTensorElementAugmentation A X P Q).app
        (c.obj ((withoutFirst I).max' (withoutFirst_nonempty hI h0))))).f k
        (k.negOnePow • strictRawModuleTensorElementSelectedCochainAtMax A X P Q c (withoutFirst I) k
          (withoutFirst_nonempty hI h0) (by have := card_withoutFirst I h0; omega))) := by
  have ht : ∀ (a b : Fin (n + 2)) (j : Fin (n + 1)) (ha : a = 0) (hb : b = j.succ)
      (v : GradedHom A ((strictRawModuleTensorConeData A X P Q c).obj a)
        ((strictRawModuleTensorConeData A X P Q c).obj b) k)
      (w : GradedHom A (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P)) ((strictRawModuleTensorElementDiagram A X P Q).obj (c.obj j)) k),
      HEq v w → HEq ((eHomWhiskerLeft (Complex A) (ForgetEnrichment.of (Complex A) ((strictRawModuleTensorConeData A X P Q c).obj a))
        (strictRawModuleTensorConeAugmentationAt A X P Q c b)).f k v)
        ((eHomWhiskerLeft (Complex A) ((strictRawModuleProbeFunctor A X).obj P) ((strictRawModuleTensorElementAugmentation A X P Q).app (c.obj j))).f k w) := by
    intro a b j ha hb v w hv
    subst a
    subst b
    cases eq_of_heq hv
    rfl
  have hb' : b = ((withoutFirst I).max' (withoutFirst_nonempty hI h0)).succ :=
    hb.trans (max_withoutFirst I hI h0).symm
  exact ht a b _ ha0 hb' _ _
    (strictRawModuleTensorConeData_hom_mixed A X P Q c I a b k hI ha hb hk ha0 h0)

lemma strictRawModuleTensorConeAugmentationAt_quasiIso {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) (i : Fin (n + 2)) :
    moduleQuasiIso A (dgAlgebraCategory A ((assocForget A).obj X)) (strictRawModuleTensorConeAugmentationAt A X P Q c i) := by
  induction i using Fin.cases with
  | zero => exact (moduleQuasiIso A (dgAlgebraCategory A ((assocForget A).obj X))).id_mem ((strictRawModuleProbeFunctor A X).obj P)
  | succ i => exact strictRawModuleTensorElementAugmentation_weak A X P Q (c.obj i)

lemma strictRawModuleTensorConeAugmentationAt_reindex {n m : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (θ : ⦋m⦌ ⟶ ⦋n⦌) (i : Fin (m + 2)) :
    HEq (strictRawModuleTensorConeAugmentationAt A X P Q c (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom θ.toOrderHom i))
      (strictRawModuleTensorConeAugmentationAt A X P Q
        ((SimplexCategory.toCat.map θ).toFunctor ⋙ c) i) := by
  induction i using Fin.cases with
  | zero => rfl
  | succ i => rfl

end SerrePositivity.EInfinity.BarrattEccles
