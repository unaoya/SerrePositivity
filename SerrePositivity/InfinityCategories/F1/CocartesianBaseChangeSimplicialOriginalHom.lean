module

public import SerrePositivity.InfinityCategories.F1.CocartesianBaseChangeSimplicialHomTransportRestriction

/-!
概要：任意の単体集合への底制限後も、元の全 Hom の分類作用と底変換後の同じ作用を結ぶ。
方針：指定した元の大域自然性を制限し、同じ Hom 輸送の制限自然性と合成する。
規約：既存の大域比較を選び直さず、元の全相対 Hom を保持する。
使われ方：単体の境界を通常圏の nerve と仮定せず、元の作用の相対比較を構成する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

variable {D C : Type u} [Category.{u} D] [Category.{u} C] {A : SSet.{u + 1}}
  (a : A ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (nerve D)) (k : D ⥤ C)
  (p q : CocartesianFibrationCategory (nerve C))
local notation "U" => cocartesianBaseChangeHomTransport k p q
local notation "R₀" => cocartesianBaseChangeSimplicialRestrictionZero a k p q
local notation "R₁" => cocartesianBaseChangeSimplicialRestrictionOne a k p q
local notation "V" => cocartesianBaseChangeSimplicialHomTransport a k p q

/-- 元の全 Hom 上で、任意の単体写像への制限と同じ底変換比較は関手同型で可換。 -/
def cocartesianBaseChangeSimplicialOriginalHomIso :
    FunctorIso (((SSet.uliftFunctor.{u + 1, u}).map
    ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).map p q) ≫
      cocartesianStraighteningHomInterval
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q)) ≫ R₁ ≫ V)
      (cocartesianStraighteningHomInterval p q ≫
        intervalDiagramRestriction ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap k))
          (cocartesianStrictTransportCoherentDiagram p.val.hom)
          (cocartesianStrictTransportCoherentDiagram q.val.hom) ≫ R₀) := by
  have h₁ : FunctorIso (((SSet.uliftFunctor.{u + 1, u}).map
    ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).map p q) ≫
      cocartesianStraighteningHomInterval
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q)) ≫ R₁ ≫ V) (((SSet.uliftFunctor.{u + 1, u}).map
    ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).map p q) ≫
      cocartesianStraighteningHomInterval
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q)) ≫ U ≫ R₀) :=
    F2.functorIsoOfEq
      (((cocartesianBaseChangeHomTransport_simplicialRestrictionIso a k p q).precomp ((SSet.uliftFunctor.{u + 1, u}).map
    ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).map p q) ≫
      cocartesianStraighteningHomInterval
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q))).symm)
      (by simp only [Category.assoc]) (by simp only [Category.assoc])
  have h₀ : FunctorIso (((SSet.uliftFunctor.{u + 1, u}).map
    ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).map p q) ≫
      cocartesianStraighteningHomInterval
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q)) ≫ U ≫ R₀)
      (cocartesianStraighteningHomInterval p q ≫
        intervalDiagramRestriction ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap k))
          (cocartesianStrictTransportCoherentDiagram p.val.hom)
          (cocartesianStrictTransportCoherentDiagram q.val.hom) ≫ R₀) :=
    F2.functorIsoOfEq ((cocartesianBaseChangeHomNaturalityIso k p q).postcomp R₀)
      (by simp only [Category.assoc]) (by simp only [Category.assoc])
  exact h₁ ≪≫ h₀

end SerrePositivity.InfinityCategories
