module

public import SerrePositivity.KST.Spectra.PointedWeightedEnd
public import SerrePositivity.KST.Spectra.EndInternalHom
public import SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeTarget
public import SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeSecondSource

/-!
概要：点つき内部 Hom と自由基点を加えた重みの end の交換同型。
方針：内部 Hom と end を交換し、二重内部 Hom の二つの源を交換する。
規約：任意の重みと点つき図式での通常の圏の同型。
使われ方：HA §1.4.2、BF 1978 §2。hG・Tot の loop と段ごとの end の交換。
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet Opposite
open scoped MonoidalClosed

namespace SerrePositivity.KST.Spectra.PointedWeightedEnd

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

local instance weightedEndCotensorPointedSelfEnrichment :
    EnrichedOrdinaryCategory PointedSimplicialSet.{u} PointedSimplicialSet.{u} :=
  enrichedOrdinaryCategorySelf PointedSimplicialSet.{u}

variable {I : Type u} [SmallCategory I]

/-- 概要：点つき内部 Hom を end の図式へ施すと、係数への内部 Hom と自然同型。
方針：二つの源の交換同型の源・標的の自然性を二変数の図式で使う。
規約：重みの自由基点と固定した点つき源の順序を交換する。
使われ方：HA §1.4.2。end の loop 交換の成分の比較。 -/
def cotensorDiagramIso (A : PointedSimplicialSet.{u}) (W : I ⥤ SSet.{u})
    (D : I ⥤ PointedSimplicialSet.{u}) :
    EndInternalHom.postDiagram (ihom A) (diagram W D) ≅ diagram W (D ⋙ ihom A) :=
  NatIso.ofComponents
    (fun i ↦ NatIso.ofComponents
      (fun j ↦ _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso A (PointedObject.adjoin (W.obj i.unop)) (D.obj j))
      (fun f ↦ by
        dsimp only [EndInternalHom.postDiagram, diagram, Enriched.FunctorCategory.diagram,
          eHomFunctor, Functor.comp, Functor.op, Functor.whiskeringLeft, Functor.whiskeringRight]
        simp only [enrichedOrdinaryCategorySelf_eHomWhiskerLeft]
        exact _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeTarget.natural_post _ _ _))
    (fun f ↦ by
      apply NatTrans.ext
      funext j
      dsimp only [EndInternalHom.postDiagram, diagram, Enriched.FunctorCategory.diagram,
        eHomFunctor, Functor.comp, Functor.op, Functor.whiskeringLeft, Functor.whiskeringRight,
        NatTrans.comp_app, NatIso.ofComponents_hom_app]
      simp only [enrichedOrdinaryCategorySelf_eHomWhiskerRight]
      exact _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeSecondSource.natural_pre_right _ _ _)

/-- 概要：点つき重み付き end と内部 Hom の交換同型。
方針：内部 Hom の end 保存と二重 Hom の源交換を合成する。
規約：loop の場合を含み、Kan 性に依存しない。
使われ方：HA §1.4.2、BF 1978 §2。hG・Tot の随伴構造射の Ω 条件。 -/
def cotensorIso (A : PointedSimplicialSet.{u}) (W : I ⥤ SSet.{u})
    (D : I ⥤ PointedSimplicialSet.{u}) :
    (ihom A).obj (obj W D) ≅ obj W (D ⋙ ihom A) :=
  EndInternalHom.iso A (diagram W D) ≪≫
    (endFunctor I PointedSimplicialSet.{u}).mapIso (cotensorDiagramIso A W D)

end

end SerrePositivity.KST.Spectra.PointedWeightedEnd
