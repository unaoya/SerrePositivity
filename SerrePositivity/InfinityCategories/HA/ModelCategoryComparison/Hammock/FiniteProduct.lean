module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.WeakTensor
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
/-!
# 元の有限個の単体集合の直積と比較射の弱同値性

概要：有限個の元の単体集合の点ごとの依存積と元の比較射を構成する。
方針：先頭と残りの直積との同型で帰納し、既存の二項直積の弱同値保存を使う。
規約：空積を含み、元の比較射自身を判定する。
使われ方：DK10.6(ii)の固定頂点列に沿う隣接 Hom の有限直積。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FiniteProduct
open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.SerrePositivity.InfinityCategories
variable {k : ℕ} (A : Fin k → SSet.{u})
def space : SSet.{u} where
  obj n := ∀ i, (A i).obj n
  map θ := ↾fun x i => (A i).map θ (x i)
  map_id n := by ext x i; exact (A i).map_id_apply n (x i)
  map_comp θ φ := by ext x i; exact (A i).map_comp_apply θ φ (x i)
variable {A} {B : Fin k → SSet.{u}} (η : ∀ i, A i ⟶ B i)
def map : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FiniteProduct.space A ⟶ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FiniteProduct.space B where
  app n := ↾fun x i => (η i).app n (x i)
  naturality n m θ := by
    apply ConcreteCategory.hom_ext
    intro x
    funext i
    exact ConcreteCategory.congr_hom ((η i).naturality θ) (x i)

def splitIso (A : Fin (k + 1) → SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FiniteProduct.space A ≅ A 0 ⊗ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FiniteProduct.space (fun i : Fin k => A i.succ) :=
  NatIso.ofComponents (fun n => Equiv.toIso
    { toFun x := (x 0, fun i => x i.succ)
      invFun x := Fin.cases x.1 x.2
      left_inv x := by funext i; cases i using Fin.cases <;> rfl
      right_inv x := rfl }) (by intro n m θ; ext x; rfl)

lemma splitIso_naturality {A B : Fin (k + 1) → SSet.{u}} (η : ∀ i, A i ⟶ B i) :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FiniteProduct.map η ≫ (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FiniteProduct.splitIso B).hom =
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FiniteProduct.splitIso A).hom ≫ (η 0 ⊗ₘ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FiniteProduct.map (fun i : Fin k => η i.succ)) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro x
  rfl

def emptyIso (A B : Fin 0 → SSet.{u}) : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FiniteProduct.space A ≅ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FiniteProduct.space B where
  hom := { app := fun _ => ↾(fun _ i => Fin.elim0 i)
           naturality := by
             intros
             apply ConcreteCategory.hom_ext
             intro x
             funext i
             exact Fin.elim0 i }
  inv := { app := fun _ => ↾(fun _ i => Fin.elim0 i)
           naturality := by
             intros
             apply ConcreteCategory.hom_ext
             intro x
             funext i
             exact Fin.elim0 i }
  hom_inv_id := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro x
    funext i
    exact Fin.elim0 i
  inv_hom_id := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro x
    funext i
    exact Fin.elim0 i

lemma map_weak (η : ∀ i, A i ⟶ B i) (hη : ∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (η i)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FiniteProduct.map η) := by
  induction k with
  | zero =>
    have h : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FiniteProduct.map η = (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FiniteProduct.emptyIso A B).hom := by
      apply NatTrans.ext
      funext n
      apply ConcreteCategory.hom_ext
      intro x
      funext i
      exact Fin.elim0 i
    rw [h]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FiniteProduct.emptyIso A B)).isWeakHomotopyEquivalence
  | succ k ih =>
    have ht := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.weakTensor (hη 0) (ih (fun i : Fin k => η i.succ) (fun i => hη i.succ))
    have hc := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FiniteProduct.splitIso A)).isWeakHomotopyEquivalence.comp ht
    rw [← _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FiniteProduct.splitIso_naturality η] at hc
    have hb := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FiniteProduct.splitIso B)).isWeakHomotopyEquivalence
    exact hb.cancel_right hc
end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FiniteProduct
