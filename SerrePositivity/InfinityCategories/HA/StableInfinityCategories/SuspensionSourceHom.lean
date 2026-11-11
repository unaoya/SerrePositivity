module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionObjectComparison

/-! # Suspension 図式への始点の射の持ち上げ

概要：始点の射を指定 suspension 図式間の h の射へ一意に持ち上げる。
方針：始点評価の圏同値の充満忠実性を用いる。
規約：始点の指定の等号による輸送を含める。
使われ方：Σ の関手性と接続射の自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：指定した二つの suspension の始点の射を図式間の射へ持ち上げる。
方針：始点評価の圏同値の充満性で、等号で輸送した射の逆像を取る。
規約：始点評価で一意に定まる。使われ方：Σ の射と図式の比較の照合。 -/
def SuspensionSquare.liftSourceHom {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    {x y : X _⦋0⦌} (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare x) (r : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare y)
    (f : SSet.HomotopyCategory.mk x ⟶ SSet.HomotopyCategory.mk y) :
    (SSet.HomotopyCategory.mk s.diagramVertex : hoFunctor.obj (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.suspensionDiagrams X)) ⟶
      SSet.HomotopyCategory.mk r.diagramVertex :=
  (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionDiagramSourceEquivalence X).toHoEquivalence.functor.preimage
    (eqToHom (congrArg SSet.HomotopyCategory.mk
      ((s.diagramVertex_evaluation 0 0).trans s.source_eq)) ≫
      f ≫ eqToHom (congrArg SSet.HomotopyCategory.mk
        ((r.diagramVertex_evaluation 0 0).trans r.source_eq).symm))

/-- 概要：始点評価で持ち上げた射を戻すと始点の表示で輸送した元の射になる。
方針：充満な関手の逆像の式。
規約：任意の始点の射。使われ方：接続射の自然性の始点条件。 -/
lemma SuspensionSquare.liftSourceHom_source {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    {x y : X _⦋0⦌} (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare x) (r : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare y)
    (f : SSet.HomotopyCategory.mk x ⟶ SSet.HomotopyCategory.mk y) :
    (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.suspensionDiagramEvaluation X 0 0)).toFunctor.map (s.liftSourceHom r f) =
      eqToHom (congrArg SSet.HomotopyCategory.mk
      ((s.diagramVertex_evaluation 0 0).trans s.source_eq)) ≫
        f ≫ eqToHom (congrArg SSet.HomotopyCategory.mk
          ((r.diagramVertex_evaluation 0 0).trans r.source_eq).symm) :=
  (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionDiagramSourceEquivalence X).toHoEquivalence.functor.map_preimage _

/-- 概要：始点評価の切断の後で射影した h の射は元の射と Arrow として一致する。
方針：単体的な切断の式で合成を恒等射に戻し、辺の代表を計算する。
規約：端点の表示の輸送を含める。使われ方：図式の対象比較の自然性。 -/
lemma suspensionSourceSectionHoMap_source_arrow {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    {x y : X _⦋0⦌} (f : SSet.HomotopyCategory.mk x ⟶ SSet.HomotopyCategory.mk y) :
    Arrow.mk ((hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.suspensionDiagramEvaluation X 0 0)).toFunctor.map
      ((hoFunctor.map (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionDiagramSourceEquivalence X).inv).toFunctor.map f)) =
        Arrow.mk f := by
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHoMap_comp]
  have hi := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHoMap_congr_arrow (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionDiagramSourceEquivalence_inv_source X) f
  have hid : (hoFunctor.map (𝟙 X)).toFunctor.map f = f := by
    obtain ⟨e, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective x y f
    rfl
  exact hi.trans (congrArg Arrow.mk hid)

/-- 概要：切断の後で射影した h の射は切断の始点等号による輸送で記述できる。
方針：元の射との Arrow の等号から端点の輸送を取り出す。
規約：切断自体の厳密性の式を使う。使われ方：対象比較と射の可換式の計算。 -/
lemma suspensionSourceSectionHoMap_source {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    {x y : X _⦋0⦌} (f : SSet.HomotopyCategory.mk x ⟶ SSet.HomotopyCategory.mk y) :
    (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.suspensionDiagramEvaluation X 0 0)).toFunctor.map
      ((hoFunctor.map (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionDiagramSourceEquivalence X).inv).toFunctor.map f) =
        eqToHom (congrArg SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionSourceSectionVertex_source x)) ≫
          f ≫ eqToHom (congrArg SSet.HomotopyCategory.mk
            (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionSourceSectionVertex_source y).symm) := by
  obtain ⟨hX, hY, hf⟩ := (Arrow.mk_eq_mk_iff _ _).mp (suspensionSourceSectionHoMap_source_arrow f)
  exact hf

/-- 概要：図式の対象比較は始点の射とその指定図式への持ち上げに関して可換。
方針：始点評価の忠実性で両辺を比較し、等号による輸送を合成する。
規約：始点の二頂点は異なってよい。使われ方：Σ に値を持つ対象比較の自然性。 -/
lemma SuspensionSquare.sourceDiagramObjIso_naturality {X : SSet.{u}}
    [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] {x y : X _⦋0⦌} (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare x) (r : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare y)
    (f : SSet.HomotopyCategory.mk x ⟶ SSet.HomotopyCategory.mk y) :
    s.sourceDiagramObjIso.hom ≫ s.liftSourceHom r f =
      (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionDiagramSourceEquivalence X).inv).toFunctor.map f ≫
        r.sourceDiagramObjIso.hom := by
  apply (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionDiagramSourceEquivalence X).toHoEquivalence.functor.map_injective
  change (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.suspensionDiagramEvaluation X 0 0)).toFunctor.map _ =
    (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.suspensionDiagramEvaluation X 0 0)).toFunctor.map _
  rw [Functor.map_comp, Functor.map_comp, liftSourceHom_source, suspensionSourceSectionHoMap_source]
  change ((hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.suspensionDiagramEvaluation X 0 0)).toFunctor.mapIso
      s.sourceDiagramObjIso).hom ≫ _ = _ ≫
    ((hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.suspensionDiagramEvaluation X 0 0)).toFunctor.mapIso r.sourceDiagramObjIso).hom
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare.sourceDiagramObjIso_source, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare.sourceDiagramObjIso_source]
  simp only [eqToIso.hom, Category.assoc, eqToHom_trans, eqToHom_trans_assoc]

/-- 概要：S3 の対象比較同型は始点の射と指定 suspension 図式への持ち上げで可換。
方針：図式での自然性を終点で評価し、対象比較の終点の式を使う。
規約：Σ の射への作用は既存 suspensionFunctor のもの。
使われ方：接続射を Σ へ移した自然性。 -/
lemma SuspensionSquare.suspensionFunctorObjIso_naturality {X : SSet.{u}}
    [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] {x y : X _⦋0⦌} (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare x) (r : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare y)
    (f : SSet.HomotopyCategory.mk x ⟶ SSet.HomotopyCategory.mk y) :
    s.suspensionFunctorObjIso.hom ≫
      (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.suspensionDiagramEvaluation X 1 1)).toFunctor.map (s.liftSourceHom r f) =
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionFunctor X).map f ≫ r.suspensionFunctorObjIso.hom := by
  have h := congrArg (fun a ↦ (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.suspensionDiagramEvaluation X 1 1)).toFunctor.map a)
    (s.sourceDiagramObjIso_naturality r f)
  rw [Functor.map_comp, Functor.map_comp] at h
  change ((hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.suspensionDiagramEvaluation X 1 1)).toFunctor.mapIso
      s.sourceDiagramObjIso).hom ≫ _ = (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionFunctor X).map f ≫
    ((hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.suspensionDiagramEvaluation X 1 1)).toFunctor.mapIso
      r.sourceDiagramObjIso).hom at h
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare.sourceDiagramObjIso_target, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare.sourceDiagramObjIso_target] at h
  exact h

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
