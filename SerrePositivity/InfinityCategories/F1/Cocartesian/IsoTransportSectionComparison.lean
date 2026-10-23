module

public import SerrePositivity.InfinityCategories.F1.FunctorCategories.IsoTransportQuasicategoryComparison
public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeNativeSectionPostHom

/-!
概要：同じ二重・直接引き戻しの結合同型を、全局所 Hom に自然な section 評価の比較へ移す。
方針：指定同型の始域の全 Hom を保持する豊穣圏を使い、元の成分を回収する。
規約：元の結合同型と既存の section 結合比較を変更しない。
使われ方：同じ結合 Hom 輸送を全局所 Hom の分類作用と比較する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 元の全 cocartesian Hom を保持した、指定同型の section 評価の豊穣比較。 -/
def cocartesianIsoTransportSectionComparison {B : SSet.{u}} (a : Over B) :
    QuasicategoryEnrichedComparison
      ((isoTransportSourceEnriched SSet.{u} (CocartesianFibrationObject B)).comp SSet
        (cocartesianSectionsEnrichedEvaluation a))
      ((isoTransportTargetEnriched SSet.{u} (CocartesianFibrationObject B)).comp SSet
        (cocartesianSectionsEnrichedEvaluation a)) :=
  isoTransportQuasicategoryComparison (cocartesianSectionsEnrichedEvaluation a)

/-- 元の二重・直接引き戻しと同じ全空間の結合同型を、指定同型の対象として扱う。 -/
def cocartesianBaseChangeIsoTransportObject
    {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
    (l : A ⥤ D) (k : D ⥤ C) (p : CocartesianFibrationCategory (nerve C)) :
    IsoTransportObject (CocartesianFibrationObject (nerve A)) where
  source := (cocartesianFibrationBaseChangeCoreEnriched (nerveMap l)).obj
    ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)
  target := (cocartesianFibrationBaseChangeCoreEnriched (nerveMap (l ⋙ k))).obj p
  comparison := cocartesianBaseChangeNativeObjectIso l k p

/-- 全局所 Hom に自然な同じ比較の成分は、既存の section 結合比較そのもの。 -/
lemma cocartesianIsoTransportSectionComparison_native_component
    {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
    (l : A ⥤ D) (k : D ⥤ C) (p : CocartesianFibrationCategory (nerve C)) (a : A) :
    (cocartesianIsoTransportSectionComparison (Over.mk (nerveMap (Under.forget a)))).val
      (cocartesianBaseChangeIsoTransportObject l k p) =
    (cocartesianBaseChangeAssociativityComponent p.val.hom l k a).hom := by
  apply (functorVertexEquiv _ _).injective
  have h := enrichedOrdinaryFunctor_map_unit SSet.{u}
    (cocartesianSectionsEnrichedEvaluation (Over.mk (nerveMap (Under.forget a))))
    (cocartesianBaseChangeIsoTransportObject l k p).comparison.hom
  have hc := congrArg (SSet.unitHomEquiv _)
    (cocartesianBaseChangeNativeObjectIso_sectionPostHom l k p a)
  exact (congrArg (SSet.unitHomEquiv _) h).trans hc

/-- 同じ豊穣比較の源の core は、二重引き戻し間の元の全局所 Hom の core そのもの。 -/
lemma cocartesianBaseChangeIsoTransportObject_coreHom
    {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
    (l : A ⥤ D) (k : D ⥤ C) (p q : CocartesianFibrationCategory (nerve C)) :
    (quasicategoryCore (SimplicialCategory.sHom
      (cocartesianBaseChangeIsoTransportObject l k p)
      (cocartesianBaseChangeIsoTransportObject l k q)) : SSet.{u}) =
    SimplicialCategory.sHom
      ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap l)).obj
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p))
      ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap l)).obj
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q)) := rfl

end SerrePositivity.InfinityCategories
