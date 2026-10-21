module

public import SerrePositivity.EInfinity.Hammock.UnmarkedEmptySpace

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
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.AllMarked
open CategoryTheory

variable {C : Type u} [Category.{u} C] (W : MorphismProperty C) (X Y : Paths C)

def emptyValueMap : nativeSpace W X Y ⟶ EmptyValue.space W X Y where
  app n := ↾fun x => ⟨(inclusion W X Y).app n x, (inclusion_range W X Y n _).1 ⟨x, rfl⟩⟩
  naturality n m θ := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    exact congrArg (fun k => k x) ((inclusion W X Y).naturality θ)

lemma emptyValueMap_bijective (n : SimplexCategoryᵒᵖ) :
    Function.Bijective ((emptyValueMap W X Y).app n) := by
  constructor
  · intro x y h
    exact inclusion_injective W X Y n (congrArg Subtype.val h)
  · intro y
    obtain ⟨x, hx⟩ := (inclusion_range W X Y n y.val).2 y.property
    exact ⟨x, Subtype.ext hx⟩

def emptyIso : nativeSpace W X Y ≅ EmptyValue.space W X Y :=
  NatIso.ofComponents (fun n => (Equiv.ofBijective ((emptyValueMap W X Y).app n)
    (emptyValueMap_bijective W X Y n)).toIso) (fun θ => (emptyValueMap W X Y).naturality θ)

lemma emptyIso_hom_inclusion :
    (emptyIso W X Y).hom ≫ EmptyValue.inclusion W X Y = inclusion W X Y := rfl

def emptyLift : EmptyValue.space W X Y ⟶ nativeSpace W X Y := (emptyIso W X Y).inv

lemma emptyLift_inclusion : emptyLift W X Y ≫ inclusion W X Y = EmptyValue.inclusion W X Y := by
  rw [← emptyIso_hom_inclusion, emptyLift, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

lemma emptyValueMap_emptyLift : emptyValueMap W X Y ≫ emptyLift W X Y = 𝟙 (nativeSpace W X Y) :=
  (emptyIso W X Y).hom_inv_id

lemma emptyLift_unique (n : SimplexCategoryᵒᵖ) (x : (EmptyValue.space W X Y).obj n)
    (z : (nativeSpace W X Y).obj n) (hz : (inclusion W X Y).app n z = x.val) :
    z = (emptyLift W X Y).app n x := by
  apply inclusion_injective W X Y n
  exact hz.trans (congrArg (fun k => k.app n x) (emptyLift_inclusion W X Y)).symm

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.AllMarked
