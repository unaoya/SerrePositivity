module
public import SerrePositivity.InfinityCategories.Stable.LoopConeSourceFiber
public import SerrePositivity.InfinityCategories.F1B.KanUnitCommaFiberLeftFibration
public import SerrePositivity.InfinityCategories.F1B.KanVertexFiberSquareIso
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftUnstraighteningFiberIso
public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftFibrationFiberComparison
/-!
概要：実 loop 錐の comma 比較を図式固定 fiber へ制限する。
方針：二段の厳密 fiber と pullback の同型を照合し、同じ実射に F1 の判定を適用する。
規約：fiber 同値性の仮定を明示し、まだ全錐比較の同値性とは主張しない。
使われ方：一般安定性判定の実境界比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 同じ実 comma 比較を、loop 図式固定の厳密 fiber へ制限する。 -/
def loopConeClassifierDiagramFiberMap (X : SSet.{u}) [Quasicategory X] (x : X _⦋0⦌)
    (d : (loopDiagrams X) _⦋0⦌) :
    vertexFiber (loopConeSourceFiberProjection X x) d ⟶
      vertexFiber (F1B.kanUnitCommaFiberProjection (loopDiagramEvaluation X 0 0) x) d :=
  vertexFiberMap (loopConeSourceFiberProjection X x)
    (F1B.kanUnitCommaFiberProjection (loopDiagramEvaluation X 0 0) x)
    (loopConeClassifierSourceFiberMap X x) (by
      simpa only [F1B.kanUnitCommaFiberProjection, Category.assoc,
        loopConeSourceFiberProjection] using loopConeClassifierSourceFiberMap_target X x) d

/-- 図式固定 fiber を、固定錐頂点からの対応する錐 fiber と同型にする。 -/
def loopConeSourceDiagramFiberIso (X : SSet.{u}) [Quasicategory X] (x : X _⦋0⦌)
    (d : (loopDiagrams X) _⦋0⦌) :
    vertexFiber (loopConeSourceFiberProjection X x) d ≅
      vertexFiber (pointedConeProjection (horn 2 2 : SSet.{u}) X x)
        ((loopDiagramConeFamily X ≫ limitConeProjection (horn 2 2 : SSet.{u}) X).app
          (Opposite.op ⦋0⦌) d) := by
  let q := pointedConeProjection (horn 2 2 : SSet.{u}) X x
  let P := loopDiagramConeFamily X ≫ limitConeProjection (horn 2 2 : SSet.{u}) X
  let e := (loopConeSourceFiber_isPullback X x).isoPullback
  have he : loopConeSourceFiberProjection X x ≫ (Iso.refl (loopDiagrams X)).hom =
      e.hom ≫ pullback.snd q P := by
    simpa only [Iso.refl_hom, Category.comp_id] using
      (loopConeSourceFiber_isPullback X x).isoPullback_hom_snd.symm
  exact F1B.kanVertexFiberSquareIso (loopConeSourceFiberProjection X x) (pullback.snd q P)
    e (Iso.refl _) he d ≪≫ vertexFiberPullbackIso q P d
/-- 図式固定 fiber 同型は元の実錐への包含と可換。 -/
lemma loopConeSourceDiagramFiberIso_hom_ι (X : SSet.{u}) [Quasicategory X] (x : X _⦋0⦌)
    (d : (loopDiagrams X) _⦋0⦌) :
    (loopConeSourceDiagramFiberIso X x d).hom ≫
      vertexFiberι (pointedConeProjection (horn 2 2 : SSet.{u}) X x)
        ((loopDiagramConeFamily X ≫ limitConeProjection (horn 2 2 : SSet.{u}) X).app
          (Opposite.op ⦋0⦌) d) =
      vertexFiberι (loopConeSourceFiberProjection X x) d ≫ loopConeSourceFiberDiagram X x := by
  dsimp only [loopConeSourceDiagramFiberIso, Iso.trans_hom]
  rw [Category.assoc, vertexFiberPullbackIso_hom_ι, ← Category.assoc]
  simp only [F1B.kanVertexFiberSquareIso, F1B.kanVertexFiberSquareHom,
    Iso.refl_hom, NatTrans.id_app, CategoryTheory.types_id_apply, Category.assoc]
  rw [← Category.assoc, vertexFiberLift_ι, Category.assoc, IsPullback.isoPullback_hom_fst]

/-- 図式固定 fiber の比較は元の実 comma 比較への包含と可換。 -/
lemma loopConeClassifierDiagramFiberMap_ι (X : SSet.{u}) [Quasicategory X] (x : X _⦋0⦌)
    (d : (loopDiagrams X) _⦋0⦌) :
    loopConeClassifierDiagramFiberMap X x d ≫
      vertexFiberι (F1B.kanUnitCommaFiberProjection (loopDiagramEvaluation X 0 0) x) d =
      vertexFiberι (loopConeSourceFiberProjection X x) d ≫ loopConeClassifierSourceFiberMap X x :=
  vertexFiberMap_ι _ _ _ _ _
/-- 同じ実 fiber 比較が各図式上で同値なら、始点固定比較も同値。 -/
lemma loopConeClassifierSourceFiberMap_isQCatEquivalence_of_diagramFibers
    (X : SSet.{u}) [Quasicategory X] (x : X _⦋0⦌)
    (h : ∀ d : (loopDiagrams X) _⦋0⦌,
      IsQCatEquivalence (loopConeClassifierDiagramFiberMap X x d)) :
    IsQCatEquivalence (loopConeClassifierSourceFiberMap X x) := by
  let q := F1B.kanUnitCommaFiberProjection (loopDiagramEvaluation X 0 0) x
  let : Quasicategory (unitCommaFiber (loopDiagramEvaluation X 0 0) x) :=
    quasicategory_of_innerFibration q
  have hf : loopConeClassifierSourceFiberMap X x ≫ q = loopConeSourceFiberProjection X x := by
    simpa only [q, F1B.kanUnitCommaFiberProjection, Category.assoc,
      loopConeSourceFiberProjection] using loopConeClassifierSourceFiberMap_target X x
  exact isQCatEquivalence_of_leftFibration_fibers (loopConeSourceFiberProjection X x) q
    (loopConeClassifierSourceFiberMap X x) hf h
end SerrePositivity.InfinityCategories
