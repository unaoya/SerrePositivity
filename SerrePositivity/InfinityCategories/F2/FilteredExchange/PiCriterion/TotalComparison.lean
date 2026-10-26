module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentTotalColimit
public import SerrePositivity.InfinityCategories.F2.Presentable.NativeCoconeHomComparison

/-!
概要：構成済み全空間余錐からの比較の頂点で、元の余錐の余極限性を判定する。
方針：始対象からの射を選び、coslice 射影の可逆性反映を使う。
規約：比較は余錐全体から取り、頂点の抽象的な同型存在には置き換えない。
使われ方：filtered 全空間の π 判定を元の coherent 余錐へ戻す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.PiCriterion
variable {B : SSet.{u}}

/-- 全空間の普遍余錐から指定余錐へのホモトピー圏の比較。 -/
def totalCoconeComparison
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) (c : JoinCocone F) :
    (HomotopyCategory.mk (coherentDiagramTotalCocone F) :
      hoFunctor.obj (sliceUnder F)) ⟶ HomotopyCategory.mk c :=
  (coherentDiagramTotalCocone_isColimit F).isInitialHo.to _

/-- 同じ余錐比較の頂点射。 -/
def totalVertexComparison
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) (c : JoinCocone F) :=
  Presentable.nativeCoconeHomApex (totalCoconeComparison F c)

/-- 元の余錐は余極限であることと、全空間からの指定比較の可逆性は同値。 -/
lemma isColimitCone_iff_totalVertexComparison_isIso
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) (c : JoinCocone F) :
    IsColimitCone c ↔ IsIso (totalVertexComparison F c) := by
  constructor
  · intro hc
    exact Presentable.nativeCoconeHomApex_isIso
      (coherentDiagramTotalCocone_isColimit F) hc (totalCoconeComparison F c)
  · intro h
    exact Presentable.isColimitCone_of_nativeCoconeHomApex_isIso
      (coherentDiagramTotalCocone_isColimit F) (totalCoconeComparison F c) h

/-- 両余錐が普遍なら、指定比較は既存の余極限頂点同型の射に一致。 -/
lemma totalVertexComparison_eq_colimitVertexIso_hom
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    (c : JoinCocone F) (hc : IsColimitCone c) :
    totalVertexComparison F c =
      (colimitVertexIso (coherentDiagramTotalCocone F) c
        (coherentDiagramTotalCocone_isColimit F) hc).hom := by
  change (hoFunctor.map (sliceUnderProjection F)).toFunctor.map
      (totalCoconeComparison F c) =
    (hoFunctor.map (sliceUnderProjection F)).toFunctor.map
      (colimitConeIso (coherentDiagramTotalCocone F) c
        (coherentDiagramTotalCocone_isColimit F) hc).hom
  apply congrArg ((hoFunctor.map (sliceUnderProjection F)).toFunctor.map)
  exact (coherentDiagramTotalCocone_isColimit F).isInitialHo.hom_ext _ _

end SerrePositivity.InfinityCategories.F2.PiCriterion
