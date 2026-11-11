module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionObjectDiagramIso

/-! # S3 と S4 の suspension の対象比較の一致

概要：標準比較同型は Σ からの二つの対象比較同型の合成に一致する。
方針：対象比較を図式へ持ち上げ、始点成分による一意性で標準比較と同定する。
規約：既存の対象比較同型の定義は変更しない。
使われ方：接続射を Σ に移す際の選択独立性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：図式の対象比較を始点で写すと始点の等号による同型になる。
方針：恒等射との Arrow の等号から始点の輸送を取り出す。
規約：等号の証明の選択は区別しない。使われ方：対象比較の合成の始点での計算。 -/
lemma SuspensionSquare.sourceDiagramObjIso_source {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    {x : X _⦋0⦌} (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare x) :
    (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.suspensionDiagramEvaluation X 0 0)).toFunctor.mapIso s.sourceDiagramObjIso =
      eqToIso (congrArg SSet.HomotopyCategory.mk ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionSourceSectionVertex_source x).trans
        ((s.diagramVertex_evaluation 0 0).trans s.source_eq).symm)) := by
  apply Iso.ext
  obtain ⟨hX, hY, hf⟩ := (Arrow.mk_eq_mk_iff _ _).mp s.sourceDiagramObjIso_source_arrow
  simpa only [Functor.mapIso_hom, eqToIso.hom, eqToHom_trans, Category.id_comp] using hf

/-- 概要：suspension 図式の全部分圏の包含を h の関手として使う。
方針：頂点条件の全部分複体の包含を hoFunctor で写す。
規約：四角形の図式を変えない。使われ方：二つの比較の h の射としての照合。 -/
def suspensionDiagramHoInclusion (X : SSet.{u}) :
    hoFunctor.obj (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.suspensionDiagrams X) ⥤
      hoFunctor.obj ((ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj X) :=
  (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsSuspensionDiagramVertex).ι).toFunctor

/-- 概要：suspension 図式の包含の後の角の評価は図式の直接の評価と一致する。
方針：二つの単体的な射による h の像を合成する。
規約：任意の角と任意の h の射。使われ方：始点・終点での比較。 -/
lemma suspensionDiagramHoInclusion_evaluation {X : SSet.{u}} [Quasicategory X]
    (i j : Fin 2) {a b : (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.suspensionDiagrams X) _⦋0⦌}
    (f : SSet.HomotopyCategory.mk a ⟶ SSet.HomotopyCategory.mk b) :
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation X i j).map ((suspensionDiagramHoInclusion X).map f) =
      (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.suspensionDiagramEvaluation X i j)).toFunctor.map f := by
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHoMap_comp _ _ f

/-- 概要：Σ からの図式の対象比較の逆・順方向の合成は標準比較の h の射と一致する。
方針：始点での対象比較を eqToIso として計算し、比較の一意性を使う。
規約：同じ指定始点の二つの suspension。使われ方：終点の対象比較同型の一致。 -/
lemma SuspensionSquare.sourceDiagramObjIso_comparisonHom {X : SSet.{u}}
    [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] {x : X _⦋0⦌} (s r : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare x) :
    (suspensionDiagramHoInclusion X).map (s.sourceDiagramObjIso.inv ≫ r.sourceDiagramObjIso.hom) =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberSuspensionComparisonHom s.square s.isPushout (r.changeSource s.source_eq.symm) := by
  apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberSuspensionComparison_hom_ext s.square s.isPushout r
  change (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation X 0 0).map _ = (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation X 0 0).map _
  rw [suspensionDiagramHoInclusion_evaluation, Functor.map_comp,
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberSuspensionComparisonHom_source]
  change ((hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.suspensionDiagramEvaluation X 0 0)).toFunctor.mapIso
      s.sourceDiagramObjIso).inv ≫
    ((hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.suspensionDiagramEvaluation X 0 0)).toFunctor.mapIso
      r.sourceDiagramObjIso).hom = _
  rw [sourceDiagramObjIso_source, sourceDiagramObjIso_source]
  simp only [eqToIso.inv, eqToIso.hom, eqToHom_trans]

/-- 概要：suspension の標準比較同型は S3 の二つの対象比較同型の合成である。
方針：図式での比較の一致を最後の頂点で評価し、S3 の対象比較と照合する。
規約：同じ指定始点の二つの suspension。使われ方：接続射を Σ へ送る際の選択独立性。 -/
lemma SuspensionSquare.comparisonIso_eq_suspensionFunctorObjIso {X : SSet.{u}}
    [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] {x : X _⦋0⦌} (s r : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare x) :
    s.comparisonIso r = s.suspensionFunctorObjIso.symm ≪≫ r.suspensionFunctorObjIso := by
  apply Iso.ext
  have h := congrArg (fun f ↦ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation X 1 1).map f)
    (s.sourceDiagramObjIso_comparisonHom r)
  rw [suspensionDiagramHoInclusion_evaluation, Functor.map_comp] at h
  change ((hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.suspensionDiagramEvaluation X 1 1)).toFunctor.mapIso
      s.sourceDiagramObjIso).inv ≫
    ((hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.suspensionDiagramEvaluation X 1 1)).toFunctor.mapIso
      r.sourceDiagramObjIso).hom = (s.comparisonIso r).hom at h
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare.sourceDiagramObjIso_target, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare.sourceDiagramObjIso_target] at h
  exact h.symm

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
