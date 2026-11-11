module

public import SerrePositivity.EInfinity.Hammock.UnmarkedNonemptyImage

/-!
# 元の hammock の非空非指定文字列の部分単体集合

概要：元の colimitValue が空でない点を、そのまま部分単体集合にする。
方針：元の評価の全単体作用素への自然性を使う。
規約：元の hammock の点を値として保持する。
使われ方：全語の非空余極限との同型と元の切断射。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.NonemptyValue
open CategoryTheory

variable {C : Type u} [Category.{u} C] (W : MorphismProperty C) (X Y : Paths C)

lemma value_simplex {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m)
    (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W.paths X Y).obj n) :
    (colimitValue W X Y).app m ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W.paths X Y).map θ x) =
      (colimitValue W X Y).app n x :=
  congrArg (fun k => k x) ((colimitValue W X Y).naturality θ)

def space : SSet.{u} where
  obj n := {x : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W.paths X Y).obj n // (colimitValue W X Y).app n x ≠ []}
  map θ := ↾fun x => ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W.paths X Y).map θ x.val, by
    rw [value_simplex W X Y θ x.val]
    exact x.property⟩
  map_id n := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W.paths X Y).map_id_apply n x.val
  map_comp θ φ := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W.paths X Y).map_comp_apply θ φ x.val

def inclusion : space W X Y ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W.paths X Y where
  app _ := ↾fun x => x.val
  naturality _ _ _ := rfl

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.NonemptyValue
