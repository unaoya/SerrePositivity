module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExactFunctorSuspensionComponents
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PastingComparisonIdentity

/-! # 完全関手と懸垂の対象比較の両立

概要：懸垂図式の標準比較は、任意の指定した suspension 四角形の対象比較と可換である。
方針：始点評価の忠実性により、始点で恒等になる二つの射を同定する。
規約：元の選択済み懸垂関手と標準比較をそのまま使う。
使われ方：Σ に値を持つ接続射の保存。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：suspension 図式の h の射の後合成は全ての角の評価と可換。
方針：単体的な後合成の評価式を h に移す。
規約：X の quasicategory 性のみ。使われ方：対象比較の二つの角の計算。 -/
lemma exactFunctorSuspensionDiagrams_hoMap_evaluation {X Y : SSet.{u}} [Quasicategory X]
    (F : X ⟶ Y) [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor F] {a b : hoFunctor.obj (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.suspensionDiagrams X)}
    (f : a ⟶ b) (i j : Fin 2) :
    (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.suspensionDiagramEvaluation Y i j)).toFunctor.map
      ((hoFunctor.map (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.exactFunctorSuspensionDiagrams F)).toFunctor.map f) =
    (hoFunctor.map F).toFunctor.map
      ((hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.suspensionDiagramEvaluation X i j)).toFunctor.map f) := by
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHoMap_comp, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHoMap_comp]
  apply Arrow.mk_injective
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHoMap_congr_arrow (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.exactFunctorSuspensionDiagrams_evaluation F i j) f

/-- 概要：指定 suspension の図式の対象比較を写すと始点は像の恒等射。
方針：角の評価と後合成を交換し、元の対象比較の始点の式を写す。
規約：安定な quasicategory 間の完全関手。使われ方：始点評価による一意性。 -/
lemma exactFunctorSuspensionDiagrams_sourceObjIso_source_arrow {X Y : SSet.{u}}
    [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] [Quasicategory Y] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable Y]
    (F : X ⟶ Y) [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor F] {x : X _⦋0⦌} (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare x) :
    Arrow.mk ((hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.suspensionDiagramEvaluation Y 0 0)).toFunctor.map
      ((hoFunctor.map (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.exactFunctorSuspensionDiagrams F)).toFunctor.map
        s.sourceDiagramObjIso.hom)) =
    Arrow.mk (𝟙 (SSet.HomotopyCategory.mk (F.app (Opposite.op ⦋0⦌) x) : hoFunctor.obj Y)) := by
  rw [exactFunctorSuspensionDiagrams_hoMap_evaluation]
  have h := congrArg (hoFunctor.map F).toFunctor.mapArrow.obj s.sourceDiagramObjIso_source_arrow
  change Arrow.mk ((hoFunctor.map F).toFunctor.map
      ((hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.suspensionDiagramEvaluation X 0 0)).toFunctor.map s.sourceDiagramObjIso.hom)) =
    Arrow.mk ((hoFunctor.map F).toFunctor.map (𝟙 (SSet.HomotopyCategory.mk x))) at h
  exact h.trans (congrArg Arrow.mk ((hoFunctor.map F).toFunctor.map_id _))

/-- 概要：図式の族の懸垂比較は指定した suspension の図式の対象比較と可換。
方針：始点評価の忠実性を使い、両辺が始点で同じ恒等射となることを確認する。
規約：対象比較の選択を変更しない。使われ方：終点で評価した懸垂比較の式。 -/
lemma exactFunctorSuspensionFamilyIso_comp_sourceObjIso {X Y : SSet.{u}}
    [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] [Quasicategory Y] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable Y]
    (F : X ⟶ Y) [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor F] {x : X _⦋0⦌} (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare x) :
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.exactFunctorSuspensionFamilyIso F).toNatIso.hom.app (SSet.HomotopyCategory.mk x) ≫
        (s.map F).sourceDiagramObjIso.hom =
      (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.exactFunctorSuspensionDiagrams F)).toFunctor.map
        s.sourceDiagramObjIso.hom := by
  apply (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionDiagramSourceEquivalence Y).toHoEquivalence.functor.map_injective
  change (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.suspensionDiagramEvaluation Y 0 0)).toFunctor.map _ =
    (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.suspensionDiagramEvaluation Y 0 0)).toFunctor.map _
  apply Arrow.mk_injective
  have hc := (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.suspensionDiagramEvaluation Y 0 0)).toFunctor.map_comp
    ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.exactFunctorSuspensionFamilyIso F).toNatIso.hom.app (SSet.HomotopyCategory.mk x))
    (s.map F).sourceDiagramObjIso.hom
  exact (congrArg Arrow.mk hc).trans
    ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableArrow_comp_of_right_identity _ _ (s.map F).sourceDiagramObjIso_source_arrow).trans
      ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.exactFunctorSuspensionFamilyIso_source_component_arrow F x).trans
        (exactFunctorSuspensionDiagrams_sourceObjIso_source_arrow F s).symm))

/-- 概要：h の懸垂比較の成分は図式の族の比較を終点で評価したもの。
方針：自然同型の後合成の成分の式を使う。
規約：既存の懸垂比較の定義を展開して照合する。使われ方：対象比較との可換式。 -/
lemma exactFunctorSuspensionIso_hom_app {X Y : SSet.{u}}
    [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] [Quasicategory Y] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable Y]
    (F : X ⟶ Y) [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor F] (x : X _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.exactFunctorSuspensionIso F).hom.app (SSet.HomotopyCategory.mk x) =
      (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.suspensionDiagramEvaluation Y 1 1)).toFunctor.map
        ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.exactFunctorSuspensionFamilyIso F).toNatIso.hom.app (SSet.HomotopyCategory.mk x)) := by
  have h := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.functorIso_toNatIso_postcomp_hom_app (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.exactFunctorSuspensionFamilyIso F)
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.suspensionDiagramEvaluation Y 1 1) x
  simpa only [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.exactFunctorSuspensionIso, Iso.trans_hom, Iso.symm_hom, eqToIso.hom,
    eqToIso.inv, NatTrans.comp_app, eqToHom_app, eqToHom_refl,
    Category.id_comp, Category.comp_id] using h

/-- 概要：完全関手の懸垂比較は任意の suspension 四角形の対象比較と可換。
方針：図式上の対象比較との可換式を終点で評価する。
規約：h の関手の同じ懸垂比較を使う。使われ方：接続射の値域の照合。 -/
lemma exactFunctorSuspensionIso_comp_objIso {X Y : SSet.{u}}
    [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] [Quasicategory Y] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable Y]
    (F : X ⟶ Y) [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor F] {x : X _⦋0⦌} (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare x) :
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.exactFunctorSuspensionIso F).hom.app (SSet.HomotopyCategory.mk x) ≫
        (s.map F).suspensionFunctorObjIso.hom =
      (hoFunctor.map F).toFunctor.map s.suspensionFunctorObjIso.hom := by
  let E := (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.suspensionDiagramEvaluation Y 1 1)).toFunctor
  have hm := E.map_comp
    ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.exactFunctorSuspensionFamilyIso F).toNatIso.hom.app (SSet.HomotopyCategory.mk x))
    (s.map F).sourceDiagramObjIso.hom
  have h := hm.symm.trans
    (congrArg E.map (exactFunctorSuspensionFamilyIso_comp_sourceObjIso F s))
  have hn := h.trans (exactFunctorSuspensionDiagrams_hoMap_evaluation F s.sourceDiagramObjIso.hom 1 1)
  change E.map ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.exactFunctorSuspensionFamilyIso F).toNatIso.hom.app
      (SSet.HomotopyCategory.mk x)) ≫ (E.mapIso (s.map F).sourceDiagramObjIso).hom =
    (hoFunctor.map F).toFunctor.map
      (((hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.suspensionDiagramEvaluation X 1 1)).toFunctor.mapIso
        s.sourceDiagramObjIso).hom) at hn
  dsimp only [E] at hn
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare.sourceDiagramObjIso_target,
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare.sourceDiagramObjIso_target, ← exactFunctorSuspensionIso_hom_app F x] at hn
  exact hn

/-- 概要：懸垂への対象比較の逆射も完全関手の懸垂比較と可換。
方針：対象比較の順方向を両側から消去する。
規約：接続射の定義と同じ逆向きの対象比較。使われ方：cofiber 接続射の保存。 -/
lemma exactFunctor_map_objIso_inv_comp_suspensionIso {X Y : SSet.{u}}
    [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] [Quasicategory Y] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable Y]
    (F : X ⟶ Y) [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor F] {x : X _⦋0⦌} (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare x) :
    (hoFunctor.map F).toFunctor.map s.suspensionFunctorObjIso.inv ≫
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.exactFunctorSuspensionIso F).hom.app (SSet.HomotopyCategory.mk x) =
      (s.map F).suspensionFunctorObjIso.inv := by
  apply (cancel_mono (s.map F).suspensionFunctorObjIso.hom).1
  rw [Category.assoc, exactFunctorSuspensionIso_comp_objIso,
    ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Iso.inv_hom_id]

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
