module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.KappaSmallSubcomplexUnion
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.FiniteGeneratorPresentation
public import Mathlib.CategoryTheory.Presentable.IsCardinalFiltered

/-!
概要：全ての κ-small な部分複体を拡大できる部分族は、包含順で κ-filtered な被覆となる。
方針：κ 個未満の和を同じ部分族へ拡大して上界を取り、有限生成部分複体で被覆を確認する。
規約：包含順の通常の poset とその同じ部分複体を使う。∞ cofinal map の構成は別工程。
使われ方：終頂点を持つ小さい部分複体による cofinal 添字の構成。

対応節は Kerodon 9.1（Tag 05WY）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories

/-- 元の包含順を持つ、指定した条件を満たす κ-small な部分複体の族。 -/
def SmallSubcomplexFamily (κ : Cardinal.{u}) (X : SSet.{u}) (P : X.Subcomplex → Prop) :=
  {A : X.Subcomplex // _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall κ A.toSSet ∧ P A}

instance smallSubcomplexFamily_partialOrder (κ : Cardinal.{u}) (X : SSet.{u})
    (P : X.Subcomplex → Prop) : PartialOrder (SmallSubcomplexFamily κ X P) :=
  inferInstanceAs (PartialOrder {A : X.Subcomplex // _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall κ A.toSSet ∧ P A})

variable {κ : Cardinal.{u}} [Fact κ.IsRegular] {X : SSet.{u}} {P : X.Subcomplex → Prop}
  (hP : ∀ A : X.Subcomplex, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall κ A.toSSet →
    ∃ B : X.Subcomplex, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall κ B.toSSet ∧ P B ∧ A ≤ B)
include hP

/-- 全ての小さい部分複体を拡大できる同じ部分族は、通常の κ-filtered poset。 -/
lemma smallSubcomplexFamily_isCardinalFiltered :
    IsCardinalFiltered (SmallSubcomplexFamily κ X P) κ where
  nonempty_cocone {J} _ F hJ := by
    have hcard : Cardinal.mk J < κ := (hasCardinalLT_iff_cardinal_mk_lt J κ).mp
      (hasCardinalLT_of_hasCardinalLT_arrow hJ)
    let A : X.Subcomplex := ⨆ j, (F.obj j).val
    have hA : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall κ A.toSSet :=
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.isKappaSmall_iSup_subcomplex Fact.out hcard _ (fun j => (F.obj j).property.1)
    obtain ⟨B, hB, hPB, hAB⟩ := hP A hA
    let b : SmallSubcomplexFamily κ X P := ⟨B, hB, hPB⟩
    refine ⟨⟨b, { app j := homOfLE ?_, naturality _ _ _ := Subsingleton.elim _ _ }⟩⟩
    exact (le_iSup (fun j => (F.obj j).val) j).trans hAB

/-- 同じ部分族の上限は元の単体集合全体。 -/
lemma iSup_smallSubcomplexFamily :
    ⨆ A : SmallSubcomplexFamily κ X P, A.val = ⊤ := by
  apply top_unique
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.iSup_finiteGeneratorSubcomplex X]
  apply iSup_le
  intro s
  have hs := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.isKappaSmall_of_finite (Cardinal.IsRegular.aleph0_le (Fact.out : κ.IsRegular))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.finiteGeneratorSubcomplex X s).toSSet
  obtain ⟨A, hA, hPA, hsA⟩ := hP (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.finiteGeneratorSubcomplex X s) hs
  exact le_iSup_of_le (⟨A, hA, hPA⟩ : SmallSubcomplexFamily κ X P) hsA

omit hP in
/-- 全ての κ-small な部分複体自体は、通常の κ-filtered poset。 -/
instance allSmallSubcomplexFamily_isCardinalFiltered :
    IsCardinalFiltered (SmallSubcomplexFamily κ X (fun _ => True)) κ :=
  smallSubcomplexFamily_isCardinalFiltered (fun A hA => ⟨A, hA, trivial, le_rfl⟩)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories
