module

public import SerrePositivity.InfinityCategories.F1.CocartesianBaseChangeSimplicialHomSpan

/-!
概要：元の比較 path の同じ底制限後の Hom span による輸送。
方針：同じ一射影の全境界持ち上げから切断を取り、元の零射影へ戻す。
規約：底制限した元の path と全 Hom をそのまま使う。
使われ方：既存の元の Hom 輸送の底制限自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

variable {D C : Type u} [Category.{u} D] [Category.{u} C]
  {A : SSet.{u + 1}} (a : A ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (nerve D)) (k : D ⥤ C) (p q : CocartesianFibrationCategory (nerve C))

/-- 同じ制限した比較 Hom の一射影を厳密に戻す切断。 -/
def cocartesianBaseChangeSimplicialHomSpanOneSection :
    intervalMappingSpace
      (functorVertex (a ≫
        cocartesianStrictTransportCoherentDiagram
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p).val.hom))
      (functorVertex (a ≫
        cocartesianStrictTransportCoherentDiagram
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q).val.hom)) ⟶
      cocartesianBaseChangeSimplicialHomComparisonSpace a k p q := by
  have : TrivialKanFibration (cocartesianBaseChangeSimplicialHomSpanOne a k p q) :=
    cocartesianBaseChangeSimplicialHomSpanOne_trivialKanFibration a k p q
  exact Classical.choose (trivialKanFibration_exists_section
    (cocartesianBaseChangeSimplicialHomSpanOne a k p q))

/-- 同じ切断は、元の制限した一射影を厳密に戻す。 -/
lemma cocartesianBaseChangeSimplicialHomSpanOneSection_projection :
    cocartesianBaseChangeSimplicialHomSpanOneSection a k p q ≫
      cocartesianBaseChangeSimplicialHomSpanOne a k p q = 𝟙 _ := by
  have : TrivialKanFibration (cocartesianBaseChangeSimplicialHomSpanOne a k p q) :=
    cocartesianBaseChangeSimplicialHomSpanOne_trivialKanFibration a k p q
  exact Classical.choose_spec (trivialKanFibration_exists_section
    (cocartesianBaseChangeSimplicialHomSpanOne a k p q))

/-- 同じ底制限後の比較 Hom の span で、元の二つの分類 Hom の制限を結ぶ。 -/
def cocartesianBaseChangeSimplicialHomTransport :
    intervalMappingSpace
      (functorVertex (a ≫
        cocartesianStrictTransportCoherentDiagram
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p).val.hom))
      (functorVertex (a ≫
        cocartesianStrictTransportCoherentDiagram
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q).val.hom)) ⟶
    intervalMappingSpace
      (functorVertex (a ≫
        (SSet.uliftFunctor.{u + 1, u}).map (nerveMap k) ≫
          cocartesianStrictTransportCoherentDiagram p.val.hom))
      (functorVertex (a ≫
        (SSet.uliftFunctor.{u + 1, u}).map (nerveMap k) ≫
          cocartesianStrictTransportCoherentDiagram q.val.hom)) :=
  cocartesianBaseChangeSimplicialHomSpanOneSection a k p q ≫
    cocartesianBaseChangeSimplicialHomSpanZero a k p q

/-- 同じ底制限後の元の比較 Hom 輸送は同値。 -/
lemma cocartesianBaseChangeSimplicialHomTransport_isQCatEquivalence :
    IsQCatEquivalence (cocartesianBaseChangeSimplicialHomTransport a k p q) := by
  have : TrivialKanFibration (cocartesianBaseChangeSimplicialHomSpanOne a k p q) :=
    cocartesianBaseChangeSimplicialHomSpanOne_trivialKanFibration a k p q
  have h : IsQCatEquivalence (cocartesianBaseChangeSimplicialHomSpanOneSection a k p q) := by
    apply (isQCatEquivalence_of_trivialKanFibration
      (cocartesianBaseChangeSimplicialHomSpanOne a k p q)).cancel_right
    rw [cocartesianBaseChangeSimplicialHomSpanOneSection_projection]
    exact (QCatEquivalence.refl _).isQCatEquivalence
  have : TrivialKanFibration (cocartesianBaseChangeSimplicialHomSpanZero a k p q) :=
    cocartesianBaseChangeSimplicialHomSpanZero_trivialKanFibration a k p q
  exact h.comp (isQCatEquivalence_of_trivialKanFibration _)

end SerrePositivity.InfinityCategories
