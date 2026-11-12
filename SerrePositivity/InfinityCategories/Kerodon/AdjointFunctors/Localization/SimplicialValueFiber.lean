module

public import Mathlib.AlgebraicTopology.SimplicialSet.Basic

/-!
# 定数単体集合への元の写像の値の fiber

概要：元の単体集合の同じ値を持つ単体を部分単体集合にする。
方針：元の写像の自然性と元の各単体作用素を使う。
規約：元の単体を保持する部分型で構成する。
使われ方：元の hammock の評価の fiber。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SimplicialValueFiber
open CategoryTheory

variable {B : Type u} {X Y : SSet.{u}}
  (ℓ : X ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B) (β : B)

lemma value_simplex {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) (x : X.obj n) :
    ℓ.app m (X.map θ x) = ℓ.app n x :=
  ConcreteCategory.congr_hom (ℓ.naturality θ) x

def space : SSet.{u} where
  obj n := {x : X.obj n // ℓ.app n x = β}
  map θ := ↾fun x => ⟨X.map θ x.val, (value_simplex ℓ θ x.val).trans x.property⟩
  map_id n := by
    ext x
    exact ConcreteCategory.congr_hom (X.map_id n) x.val
  map_comp θ φ := by
    ext x
    exact ConcreteCategory.congr_hom (X.map_comp θ φ) x.val

def inclusion : space ℓ β ⟶ X where
  app _ := ↾fun x => x.val
  naturality _ _ _ := rfl

variable (μ : Y ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B) (f : X ⟶ Y) (h : f ≫ μ = ℓ)

include h in
lemma value_map (n : SimplexCategoryᵒᵖ) (x : X.obj n) : μ.app n (f.app n x) = ℓ.app n x :=
  ConcreteCategory.congr_hom
    (congrArg (fun k : X ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B => k.app n) h) x

def map : space ℓ β ⟶ space μ β where
  app n := ↾fun x => ⟨f.app n x.val, (value_map ℓ μ f h n x.val).trans x.property⟩
  naturality n m θ := by
    ext x
    apply Subtype.ext
    exact ConcreteCategory.congr_hom (f.naturality θ) x.val

lemma map_inclusion : map ℓ β μ f h ≫ inclusion μ β = inclusion ℓ β ≫ f := rfl

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SimplicialValueFiber
