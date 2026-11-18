module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SimplicialValueFiber
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.WeakFiniteUnion

/-!
# 元の値の写像による部分複体

概要：指定した値の集合を持つ元の単体の部分複体を作る。
方針：定数単体集合への自然性で単体作用素による閉性を証明する。
規約：同じ元の写像の制限と singleton の実際の fiber を保持する。
使われ方：有限個の値ごとの弱同値の貼り合わせ。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ValueSupport
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.SSet

variable {B : Type u} {X : SSet.{u}} (ℓ : X ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B)

def subcomplex (s : Set B) : X.Subcomplex where
  obj n := {x | ℓ.app n x ∈ s}
  map θ := fun x hx => by
    change ℓ.app _ (X.map θ x) ∈ s
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SimplicialValueFiber.value_simplex]
    exact hx

lemma subcomplex_empty : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ValueSupport.subcomplex ℓ ∅ = ⊥ := rfl

lemma subcomplex_union (s t : Set B) :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ValueSupport.subcomplex ℓ (s ∪ t) = _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ValueSupport.subcomplex ℓ s ⊔ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ValueSupport.subcomplex ℓ t := rfl

lemma subcomplex_inter (s t : Set B) :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ValueSupport.subcomplex ℓ (s ∩ t) = _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ValueSupport.subcomplex ℓ s ⊓ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ValueSupport.subcomplex ℓ t := rfl

lemma subcomplex_mono {s t : Set B} (h : s ⊆ t) : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ValueSupport.subcomplex ℓ s ≤ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ValueSupport.subcomplex ℓ t :=
  fun _ _ hx => h hx

lemma subcomplex_disjoint {s t : Set B} (h : Disjoint s t) :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ValueSupport.subcomplex ℓ s ⊓ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ValueSupport.subcomplex ℓ t = ⊥ := by
  rw [← _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ValueSupport.subcomplex_inter, Set.disjoint_iff_inter_eq_empty.mp h, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ValueSupport.subcomplex_empty]

def singletonFiberIso (β : B) : (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ValueSupport.subcomplex ℓ {β}).toFunctor ≅
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SimplicialValueFiber.space ℓ β :=
  NatIso.ofComponents (fun _ => Equiv.toIso
    { toFun x := ⟨x.val, x.property⟩
      invFun x := ⟨x.val, x.property⟩
      left_inv _ := rfl
      right_inv _ := rfl }) (fun _ => rfl)

variable {Y : SSet.{u}} (μ : Y ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B)
  (f : X ⟶ Y) (h : f ≫ μ = ℓ)

include h in
lemma mapsTo (s : Set B) :
    ∀ n, Set.MapsTo (f.app n) ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ValueSupport.subcomplex ℓ s).obj n) ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ValueSupport.subcomplex μ s).obj n) := by
  intro n x hx
  change μ.app n (f.app n x) ∈ s
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SimplicialValueFiber.value_map ℓ μ f h]
  exact hx

def restriction (s : Set B) : (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ValueSupport.subcomplex ℓ s).toFunctor ⟶ (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ValueSupport.subcomplex μ s).toFunctor :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.mapSubcomplex f (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ValueSupport.mapsTo ℓ μ f h s)

lemma restriction_inclusion (s : Set B) :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ValueSupport.restriction ℓ μ f h s ≫ (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ValueSupport.subcomplex μ s).ι = (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ValueSupport.subcomplex ℓ s).ι ≫ f := rfl

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ValueSupport
