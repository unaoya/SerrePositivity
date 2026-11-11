module

public import Mathlib.CategoryTheory.Enriched.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal

/-!
# 任意の圏の元の射による離散単体的豊穣化

概要：元の各 Hom を定数単体集合にして元の単位・合成を保持する。
方針：元の圏の合成公理を同じ全次数で使う。
規約：対象・射を変更せず大域 instance を追加しない。
使われ方：非指定自由部分からの豊穣関手と生成矢の像の比較。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DiscreteEnrichment
open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C]

def hom (X Y : C) : SSet.{v} := (Functor.const SimplexCategoryᵒᵖ).obj (X ⟶ Y)

def point {X Y : C} (f : X ⟶ Y) : 𝟙_ SSet.{v} ⟶ hom X Y where
  app _ := ↾fun _ => f
  naturality _ _ _ := by
    apply ConcreteCategory.hom_ext
    intro p
    rfl

def unit (X : C) : 𝟙_ SSet.{v} ⟶ hom X X := point (𝟙 X)

def composition (X Y Z : C) : hom X Y ⊗ hom Y Z ⟶ hom X Z where
  app _ := ↾fun p => p.1 ≫ p.2
  naturality _ _ _ := by
    apply ConcreteCategory.hom_ext
    intro p
    rfl

@[instance_reducible]
def enrichedCategory : EnrichedCategory SSet.{v} C where
  Hom := hom
  id := unit
  comp := composition
  id_comp X Y := by
    ext n p
    exact Category.id_comp p
  comp_id X Y := by
    ext n p
    exact Category.comp_id p
  assoc X Y Z T := by
    ext n p
    exact Category.assoc p.1 p.2.1 p.2.2

lemma point_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (λ_ (𝟙_ SSet.{v})).inv ≫ (point f ⊗ₘ point g) ≫ composition X Y Z = point (f ≫ g) := by
  ext n p
  rfl

lemma point_ext {X Y : C} {K : SSet.{v}} (f g : hom X Y ⟶ K)
    (h : ∀ p : X ⟶ Y, point p ≫ f = point p ≫ g) : f = g := by
  ext n p
  exact congrArg (fun k => k.app n PUnit.unit) (h p)

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DiscreteEnrichment
