module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeAssociativityHomSpan
public import SerrePositivity.InfinityCategories.F1.HomSpanSectionTransport

/-!
概要：元の結合比較 Hom の同じ一射影の切断による、元の Hom の輸送。
方針：同じ全境界持ち上げによる切断と零射影を合成する。
規約：同じ結合比較 path と同じ Hom span を使う。
使われ方：元の第二面の Hom 輸送を元の二回目の比較と結合比較へ分解する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

variable {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
  (l : A ⥤ D) (k : D ⥤ C) (p q : CocartesianFibrationCategory (nerve C))

/-- 元の結合比較 Hom の一射影を厳密に戻す切断。 -/
def cocartesianBaseChangeAssociativityHomSpanOneSection :
    intervalMappingSpace
      (functorVertex (cocartesianStrictTransportCoherentDiagram
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap (l ⋙ k))).obj p).val.hom))
      (functorVertex (cocartesianStrictTransportCoherentDiagram
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap (l ⋙ k))).obj q).val.hom)) ⟶
      cocartesianBaseChangeAssociativityHomComparisonSpace l k p q := by
  have : TrivialKanFibration (cocartesianBaseChangeAssociativityHomSpanOne l k p q) :=
    cocartesianBaseChangeAssociativityHomSpanOne_trivialKanFibration l k p q
  exact Classical.choose (trivialKanFibration_exists_section
    (cocartesianBaseChangeAssociativityHomSpanOne l k p q))

/-- 同じ切断は元の一射影を厳密に戻す。 -/
lemma cocartesianBaseChangeAssociativityHomSpanOneSection_projection :
    cocartesianBaseChangeAssociativityHomSpanOneSection l k p q ≫
      cocartesianBaseChangeAssociativityHomSpanOne l k p q = 𝟙 _ := by
  have : TrivialKanFibration (cocartesianBaseChangeAssociativityHomSpanOne l k p q) :=
    cocartesianBaseChangeAssociativityHomSpanOne_trivialKanFibration l k p q
  exact Classical.choose_spec (trivialKanFibration_exists_section
    (cocartesianBaseChangeAssociativityHomSpanOne l k p q))

/-- 元の結合比較辺の同じ Hom span を使い、直接の分類 Hom を二回の分類 Hom へ運ぶ。 -/
def cocartesianBaseChangeAssociativityHomTransport :
    intervalMappingSpace
      (functorVertex (cocartesianStrictTransportCoherentDiagram
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap (l ⋙ k))).obj p).val.hom))
      (functorVertex (cocartesianStrictTransportCoherentDiagram
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap (l ⋙ k))).obj q).val.hom)) ⟶
    intervalMappingSpace
      (functorVertex (cocartesianStrictTransportCoherentDiagram
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap l)).obj
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)).val.hom))
      (functorVertex (cocartesianStrictTransportCoherentDiagram
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap l)).obj
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q)).val.hom)) :=
  cocartesianBaseChangeAssociativityHomSpanOneSection l k p q ≫
    cocartesianBaseChangeAssociativityHomSpanZero l k p q

/-- 元の結合比較辺による同じ Hom 輸送は同値。 -/
lemma cocartesianBaseChangeAssociativityHomTransport_isQCatEquivalence :
    IsQCatEquivalence (cocartesianBaseChangeAssociativityHomTransport l k p q) := by
  have : TrivialKanFibration (cocartesianBaseChangeAssociativityHomSpanOne l k p q) :=
    cocartesianBaseChangeAssociativityHomSpanOne_trivialKanFibration l k p q
  have h : IsQCatEquivalence (cocartesianBaseChangeAssociativityHomSpanOneSection l k p q) := by
    apply (isQCatEquivalence_of_trivialKanFibration
      (cocartesianBaseChangeAssociativityHomSpanOne l k p q)).cancel_right
    rw [cocartesianBaseChangeAssociativityHomSpanOneSection_projection]
    exact (QCatEquivalence.refl _).isQCatEquivalence
  have : TrivialKanFibration (cocartesianBaseChangeAssociativityHomSpanZero l k p q) :=
    cocartesianBaseChangeAssociativityHomSpanZero_trivialKanFibration l k p q
  exact h.comp (isQCatEquivalence_of_trivialKanFibration _)

end SerrePositivity.InfinityCategories
