module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.ElementsDegreeFiber
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.FilteredPosetNerve
public import Mathlib.Data.Finset.Order

/-!
概要：有限部分集合の要素圏から元の離散添字への cofinal な比較。
方針：各要素の singleton を左随伴として構成する。
規約：空の添字も含め、元の要素を変更しない。
使われ方：有限余積の filtered 余極限による小余積の構成。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：有限部分集合をその要素の型へ送る関手。
方針：包含に沿って同じ要素を運ぶ。
規約：有限部分集合は包含順序の圏を持つ。
使われ方：有限余積をまとめる要素圏。 -/
def finiteSubsetFamily (I : Type u) : Finset I ⥤ Type u where
  obj s := {i // i ∈ s}
  map f := ↾fun x ↦ ⟨x.val, leOfHom f x.property⟩

/-- 概要：有限部分集合内の要素を元の離散添字へ戻す。
方針：要素圏の射が保つ同じ要素を使う。
規約：有限部分集合の選択は忘れる。
使われ方：元の小余積図式への比較。 -/
def finiteSubsetForget (I : Type u) : (finiteSubsetFamily I).Elements ⥤ Discrete I where
  obj a := Discrete.mk a.val.val
  map f := eqToHom (Discrete.ext (congrArg Subtype.val f.map_val))

/-- 概要：各離散要素をその singleton 内の同じ要素へ送る。
方針：離散関手の対象の指定を使う。
規約：追加の要素を選択しない。
使われ方：要素を忘れる関手の左随伴。 -/
def finiteSubsetSingleton (I : Type u) : Discrete I ⥤ (finiteSubsetFamily I).Elements := by
  classical
  exact Discrete.functor (fun i ↦ (finiteSubsetFamily I).elementsMk {i} ⟨i, by simp⟩)

/-- 概要：singleton と要素を忘れる関手の随伴。
方針：singleton の包含条件を同じ要素の等式と比較する。
規約：全ての射の自然性を伴う。
使われ方：小余積への native な cofinal 比較。 -/
def finiteSubsetAdjunction (I : Type u) : finiteSubsetSingleton I ⊣ finiteSubsetForget I := by
  classical
  refine Adjunction.mkOfHomEquiv {
    homEquiv := fun i a ↦ {
      toFun := fun f ↦ eqToHom (Discrete.ext (congrArg Subtype.val f.map_val))
      invFun := fun f ↦ {
        hom := homOfLE (Finset.singleton_subset_iff.mpr ?_)
        map_val := Subtype.ext (Discrete.eq_of_hom f) }
      left_inv := fun f ↦ ?_
      right_inv := fun _ ↦ Subsingleton.elim _ _ }
    homEquiv_naturality_left_symm := fun _ _ ↦ ?_
    homEquiv_naturality_right := fun _ _ ↦ Subsingleton.elim _ _ }
  · rw [Discrete.eq_of_hom f]
    exact a.val.property
  · apply Functor.Elements.Hom.ext
    subsingleton
  · apply Functor.Elements.Hom.ext
    subsingleton

/-- 概要：有限部分集合の要素圏は元の離散添字で right cofinal。
方針：singleton 随伴が与える各 comma の始対象を使う。
規約：通常の final 性だけでなく全高次の比較を得る。
使われ方：有限余積を組み立てた全余極限から元の小余積を回収する。 -/
lemma finiteSubsetForget_nerve_isRightCofinal (I : Type u) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal (nerveMap (finiteSubsetForget I)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.nerveMap_isRightCofinal_of_initial_comma
  intro i
  let adj := finiteSubsetAdjunction I
  exact ⟨StructuredArrow.mk (adj.unit.app i),
    ⟨mkInitialOfLeftAdjoint (finiteSubsetForget I) adj i⟩⟩

/-- 概要：有限部分集合の nerve は native な filtered 添字。
方針：通常の filtered poset と aleph0-filtered の同値を使う。
規約：空集合を許し、元の宇宙に留まる。
使われ方：P_Σ の既存の filtered 余極限の適用。 -/
instance finiteSubset_isFilteredInfinity (I : Type u) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsFilteredInfinity (nerve (Finset I)) := by
  have : Fact Cardinal.aleph0.IsRegular := ⟨Cardinal.isRegular_aleph0⟩
  have : IsCardinalFiltered (Finset I) Cardinal.aleph0 :=
    (isCardinalFiltered_aleph0_iff (Finset I)).mpr inferInstance
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered Cardinal.aleph0 (nerve (Finset I)) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isKappaFiltered_nerve_of_cardinalFiltered _
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isFilteredInfinity_of_isKappaFiltered le_rfl _

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
