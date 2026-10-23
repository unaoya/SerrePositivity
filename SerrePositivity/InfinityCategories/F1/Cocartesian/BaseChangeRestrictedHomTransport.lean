module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeRestrictedHomSpan

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

variable {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
  (l : A ⥤ D) (k : D ⥤ C) (p q : CocartesianFibrationCategory (nerve C))

/-- 同じ制限した比較 Hom の一射影を厳密に戻す切断。 -/
def cocartesianBaseChangeRestrictedHomSpanOneSection :
    intervalMappingSpace
      (functorVertex ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap l) ≫
        cocartesianStrictTransportCoherentDiagram
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p).val.hom))
      (functorVertex ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap l) ≫
        cocartesianStrictTransportCoherentDiagram
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q).val.hom)) ⟶
      cocartesianBaseChangeRestrictedHomComparisonSpace l k p q := by
  have : TrivialKanFibration (cocartesianBaseChangeRestrictedHomSpanOne l k p q) :=
    cocartesianBaseChangeRestrictedHomSpanOne_trivialKanFibration l k p q
  exact Classical.choose (trivialKanFibration_exists_section
    (cocartesianBaseChangeRestrictedHomSpanOne l k p q))

/-- 同じ切断は、元の制限した一射影を厳密に戻す。 -/
lemma cocartesianBaseChangeRestrictedHomSpanOneSection_projection :
    cocartesianBaseChangeRestrictedHomSpanOneSection l k p q ≫
      cocartesianBaseChangeRestrictedHomSpanOne l k p q = 𝟙 _ := by
  have : TrivialKanFibration (cocartesianBaseChangeRestrictedHomSpanOne l k p q) :=
    cocartesianBaseChangeRestrictedHomSpanOne_trivialKanFibration l k p q
  exact Classical.choose_spec (trivialKanFibration_exists_section
    (cocartesianBaseChangeRestrictedHomSpanOne l k p q))

/-- 同じ底制限後の比較 Hom の span で、元の二つの分類 Hom の制限を結ぶ。 -/
def cocartesianBaseChangeRestrictedHomTransport :
    intervalMappingSpace
      (functorVertex ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap l) ≫
        cocartesianStrictTransportCoherentDiagram
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p).val.hom))
      (functorVertex ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap l) ≫
        cocartesianStrictTransportCoherentDiagram
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q).val.hom)) ⟶
    intervalMappingSpace
      (functorVertex ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap l) ≫
        (SSet.uliftFunctor.{u + 1, u}).map (nerveMap k) ≫
          cocartesianStrictTransportCoherentDiagram p.val.hom))
      (functorVertex ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap l) ≫
        (SSet.uliftFunctor.{u + 1, u}).map (nerveMap k) ≫
          cocartesianStrictTransportCoherentDiagram q.val.hom)) :=
  cocartesianBaseChangeRestrictedHomSpanOneSection l k p q ≫
    cocartesianBaseChangeRestrictedHomSpanZero l k p q

/-- 同じ底制限後の元の比較 Hom 輸送は同値。 -/
lemma cocartesianBaseChangeRestrictedHomTransport_isQCatEquivalence :
    IsQCatEquivalence (cocartesianBaseChangeRestrictedHomTransport l k p q) := by
  have : TrivialKanFibration (cocartesianBaseChangeRestrictedHomSpanOne l k p q) :=
    cocartesianBaseChangeRestrictedHomSpanOne_trivialKanFibration l k p q
  have h : IsQCatEquivalence (cocartesianBaseChangeRestrictedHomSpanOneSection l k p q) := by
    apply (isQCatEquivalence_of_trivialKanFibration
      (cocartesianBaseChangeRestrictedHomSpanOne l k p q)).cancel_right
    rw [cocartesianBaseChangeRestrictedHomSpanOneSection_projection]
    exact (QCatEquivalence.refl _).isQCatEquivalence
  have : TrivialKanFibration (cocartesianBaseChangeRestrictedHomSpanZero l k p q) :=
    cocartesianBaseChangeRestrictedHomSpanZero_trivialKanFibration l k p q
  exact h.comp (isQCatEquivalence_of_trivialKanFibration _)

end SerrePositivity.InfinityCategories
