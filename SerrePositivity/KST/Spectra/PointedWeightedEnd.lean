module

public import SerrePositivity.KST.Spectra.FreePointedHomRestriction
public import SerrePositivity.KST.Spectra.EndRightAdjoint
public import SerrePositivity.KST.Spectra.PointedHomotopyLimitInvariance
public import Mathlib.CategoryTheory.Enriched.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Closed.Enrichment

/-!
概要：自由基点を加えた重みからの点つき enriched end と基礎 Kan end の比較。
方針：忘却の右随伴性で end を交換し、自由基点からの Hom の具体的な制限同型を施す。
規約：通常の圏の end の構成であり、∞ 極限の主張を含まない。
使われ方：HA §1.4.2、BF 1978 §2。hG・Tot の Ω 条件のための点つき閉構造の模型。
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet Opposite

open scoped MonoidalClosed

namespace SerrePositivity.KST.Spectra.PointedWeightedEnd

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

local instance weightedEndSelfEnrichment : EnrichedOrdinaryCategory SSet.{u} SSet.{u} :=
  enrichedOrdinaryCategorySelf SSet.{u}

local instance weightedEndPointedSelfEnrichment :
    EnrichedOrdinaryCategory PointedSimplicialSet.{u} PointedSimplicialSet.{u} :=
  enrichedOrdinaryCategorySelf PointedSimplicialSet.{u}

variable {I : Type u} [SmallCategory I]

/-- 概要：重みに自由基点を加えた点つき図式からの enriched Hom の二変数図式。
方針：点つき閉モノイダル圏の標準の enriched end の図式を使う。
規約：重みの Kan 性は仮定しない。
使われ方：HA §1.4.2。点つき end の通常の極限の表示。 -/
abbrev diagram (W : I ⥤ SSet.{u}) (D : I ⥤ PointedSimplicialSet.{u}) :=
  Enriched.FunctorCategory.diagram PointedSimplicialSet.{u} (W ⋙ PointedObject.adjoinFunctor) D

/-- 概要：自由基点を加えた重みからの点つき end。
方針：点つき内部 Hom の end を取る。
規約：対象と基点を通常の点つき極限で同時に構成する。
使われ方：HA §1.4.2、BF 1978 §2。loop との交換を計算する模型。 -/
def obj (W : I ⥤ SSet.{u}) (D : I ⥤ PointedSimplicialSet.{u}) : PointedSimplicialSet.{u} :=
  end_ (diagram W D)

/-- 概要：点つき内部 Hom の図式を忘れると通常の重み付き Hom の図式と自然同型。
方針：自由基点の元の成分への制限の両変数の自然性を使う。
規約：二つの添字についての自然同型。
使われ方：HA §1.4.2。点つき end の Kan 性を基礎の end へ移す。 -/
def underlyingDiagramIso (W : I ⥤ SSet.{u}) (D : I ⥤ PointedSimplicialSet.{u}) :
    EndRightAdjoint.postDiagram PointedSimplicialSet.forget (diagram W D) ≅
      Enriched.FunctorCategory.diagram SSet.{u} W (D ⋙ PointedSimplicialSet.forget) :=
  NatIso.ofComponents
    (fun i ↦ NatIso.ofComponents
      (fun j ↦ FreePointedHomRestriction.iso (W.obj i.unop) (D.obj j))
      (fun f ↦ by
        dsimp only [EndRightAdjoint.postDiagram, diagram, Enriched.FunctorCategory.diagram,
          eHomFunctor, Functor.comp, Functor.op, Functor.whiskeringLeft, Functor.whiskeringRight]
        simp only [enrichedOrdinaryCategorySelf_eHomWhiskerLeft]
        change (PointedObject.basedHomMap (PointedObject.adjoin (W.obj i.unop)) (D.map f)).right ≫
          FreePointedHomRestriction.restrict (W.obj i.unop) (D.obj _) =
          FreePointedHomRestriction.restrict (W.obj i.unop) (D.obj _) ≫
            (ihom (W.obj i.unop)).map (D.map f).right
        exact FreePointedHomRestriction.natural_post _ _))
    (fun f ↦ by
      apply NatTrans.ext
      funext j
      dsimp only [EndRightAdjoint.postDiagram, diagram, Enriched.FunctorCategory.diagram,
        eHomFunctor, Functor.comp, Functor.op, Functor.whiskeringLeft, Functor.whiskeringRight,
        NatTrans.comp_app, NatIso.ofComponents_hom_app]
      simp only [enrichedOrdinaryCategorySelf_eHomWhiskerRight]
      change ((pre (PointedObject.adjoinFunctor.map (W.map f.unop))).app (D.obj j)).right ≫
          FreePointedHomRestriction.restrict _ (D.obj j) =
        FreePointedHomRestriction.restrict _ (D.obj j) ≫ (pre (W.map f.unop)).app (D.obj j).right
      rw [← _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre]
      exact FreePointedHomRestriction.natural_pre _ _)

/-- 概要：点つき enriched end の基礎単体集合は通常の重み付き end と同型。
方針：忘却と end の交換の後で、二変数図式の自然同型を end に送る。
規約：全て通常の圏の実際の同型。
使われ方：HA §1.4.2、BF 1978 §2。Kan 性と π_* 同型保存を点つき模型へ移す。 -/
def underlyingIso (W : I ⥤ SSet.{u}) (D : I ⥤ PointedSimplicialSet.{u}) :
    (obj W D).right ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections W (D ⋙ PointedSimplicialSet.forget) :=
  EndRightAdjoint.iso PointedObject.adjoinForgetAdjunction (diagram W D) ≪≫
    (endFunctor I SSet.{u}).mapIso (underlyingDiagramIso W D)

/-- 概要：Bousfield–Kan の重みによる点つき enriched end は Kan。
方針：基礎の end との実際の同型で、既存のホーン充填による Kan 性を移す。
規約：係数が段ごとに Kan であることを仮定する。
使われ方：BF 1978 §2、HA §1.4.2、Kerodon 7.5.4.6（Tag 03BB）。hG・Tot の Ω 列の各段。 -/
instance kanComplex (D : I ⥤ PointedSimplicialSet.{u}) [∀ i, KanComplex (D.obj i).right] :
    KanComplex (obj (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) D).right := by
  let : ∀ i, KanComplex ((D ⋙ PointedSimplicialSet.forget).obj i) :=
    fun i ↦ inferInstanceAs (KanComplex (D.obj i).right)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.kanComplex_of_iso
    (underlyingIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) D).symm

end

end SerrePositivity.KST.Spectra.PointedWeightedEnd
