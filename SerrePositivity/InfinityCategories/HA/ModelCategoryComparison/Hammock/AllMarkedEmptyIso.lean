module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedEmptySpace

/-!
# 実際の指定部分圏の hammock と元の空文字列部分との同型

概要：元の包含を空文字列部分への単体集合の同型に制限し、元の点の持ち上げを回収する。
方針：同じ包含の単射性と像の完全な判定を各次数の全単射に渡す。
規約：同型の後の包含は元の相対関手による包含自身である。
使われ方：反復切断の終端を実際の指定部分圏の hammock へ戻す。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked
open _root_.CategoryTheory

variable {C : Type u} [Category.{u} C] (W : MorphismProperty C) (X Y : Paths C)

def emptyValueMap : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.nativeSpace W X Y ⟶ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.EmptyValue.space W X Y where
  app n := ↾fun x => ⟨(_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.inclusion W X Y).app n x, (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.inclusion_range W X Y n _).1 ⟨x, rfl⟩⟩
  naturality n m θ := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    exact congrArg (fun k => k x) ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.inclusion W X Y).naturality θ)

lemma emptyValueMap_bijective (n : SimplexCategoryᵒᵖ) :
    Function.Bijective ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.emptyValueMap W X Y).app n) := by
  constructor
  · intro x y h
    exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.inclusion_injective W X Y n (congrArg Subtype.val h)
  · intro y
    obtain ⟨x, hx⟩ := (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.inclusion_range W X Y n y.val).2 y.property
    exact ⟨x, Subtype.ext hx⟩

def emptyIso : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.nativeSpace W X Y ≅ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.EmptyValue.space W X Y :=
  NatIso.ofComponents (fun n => (Equiv.ofBijective ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.emptyValueMap W X Y).app n)
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.emptyValueMap_bijective W X Y n)).toIso) (fun θ => (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.emptyValueMap W X Y).naturality θ)

lemma emptyIso_hom_inclusion :
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.emptyIso W X Y).hom ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.EmptyValue.inclusion W X Y = _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.inclusion W X Y := rfl

def emptyLift : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.EmptyValue.space W X Y ⟶ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.nativeSpace W X Y := (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.emptyIso W X Y).inv

lemma emptyLift_inclusion : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.emptyLift W X Y ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.inclusion W X Y = _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.EmptyValue.inclusion W X Y := by
  rw [← _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.emptyIso_hom_inclusion, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.emptyLift, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

lemma emptyValueMap_emptyLift : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.emptyValueMap W X Y ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.emptyLift W X Y = 𝟙 (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.nativeSpace W X Y) :=
  (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.emptyIso W X Y).hom_inv_id

lemma emptyLift_unique (n : SimplexCategoryᵒᵖ) (x : (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.EmptyValue.space W X Y).obj n)
    (z : (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.nativeSpace W X Y).obj n) (hz : (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.inclusion W X Y).app n z = x.val) :
    z = (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.emptyLift W X Y).app n x := by
  apply _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.inclusion_injective W X Y n
  exact hz.trans (congrArg (fun k => k.app n x) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.emptyLift_inclusion W X Y)).symm

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked
