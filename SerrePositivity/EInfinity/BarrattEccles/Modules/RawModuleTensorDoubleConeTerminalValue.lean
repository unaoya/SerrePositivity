module
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorDoubleConeFrontMap

/-!
概要：元の閉 augmentation の全斉次値は、二重 cone の任意作用素への制限と整合する。
方針：元の augmentation の零・後続分岐と、終端を除いた添字の回復を使う。
規約：HA Construction 1.3.1.6・1.3.1.13、同じ実 chain map の閉 cochain を保つ。使われ方：終端成分の自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open SerrePositivity.EInfinity.Modules SerrePositivity.EInfinity.ComplexLimits
open SerrePositivity.InfinityCategories.HA.Section7_1_1
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open scoped Simplicial
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorConeAugmentationClosed_reindex {n m : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (i : Fin (m + 2)) (k : ℤ) :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom (strictRawModuleTensorConeAugmentationAt A X P Q c (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom θ.toOrderHom i)) k)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom (strictRawModuleTensorConeAugmentationAt A X P Q
          ((SimplexCategory.toCat.map θ).toFunctor ⋙ c) i) k) := by
  induction i using Fin.cases with
  | zero => rfl
  | succ i => rfl

lemma strictRawModuleTensorDoubleConeTerminalValue_reindex {n m : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (i : Fin (m + 3)) (k : ℤ) (hi : i ≠ Fin.last (m + 2)) :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom (strictRawModuleTensorConeAugmentationAt A X P Q c
        ((Fin.last (n + 1)).predAboveOrderHom (doubleConeOrderHom θ i))) k)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom (strictRawModuleTensorConeAugmentationAt A X P Q
          ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)
          ((Fin.last (m + 1)).predAboveOrderHom i)) k) := by
  have ht : ∀ a b : Fin (n + 2), a = b →
      HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom (strictRawModuleTensorConeAugmentationAt A X P Q c a) k)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom (strictRawModuleTensorConeAugmentationAt A X P Q c b) k) := by
    intro a b h
    subst b
    rfl
  exact (ht _ _ (doubleConeOrderHom_predAbove θ i hi)).trans
    (strictRawModuleTensorConeAugmentationClosed_reindex A X P Q c θ _ k)

end SerrePositivity.EInfinity.BarrattEccles
