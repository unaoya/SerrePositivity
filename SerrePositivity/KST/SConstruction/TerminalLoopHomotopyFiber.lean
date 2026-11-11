module
public import SerrePositivity.KST.SConstruction.TerminalLoopPathFiber
public import SerrePositivity.KST.SConstruction.TerminalFiberContraction
public import SerrePositivity.KST.SConstruction.FiberOverContractibleBase

/-! # 終点固定 homotopy fiber への元の loop の包含
概要：元の円の loop を終点固定 homotopy fiber に含め、全空間が可縮なら全基点 π 同型を得る。
方針：始点評価の fiber 表示と pullback の基点 fiber の同型を合成する。
規約：元の円・実際の包含を使う。使われ方：元の零行 loop 射の同型性の検出。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits HomotopicalAlgebra SSet
open SSet.modelCategoryQuillen
open SerrePositivity.InfinityCategories
open Spectra

/-- 終点固定 fiber から元の全空間への射影。 -/
def terminalPathHomotopyFiberProjection {E B : PointedSimplicialSet.{u}} (f : E ⟶ B) :
    terminalPathHomotopyFiber f ⟶ E := pullback.snd (terminalPathStart B) f

/-- 終点固定 homotopy fiber の射影は Kan fibration。 -/
instance terminalPathHomotopyFiberProjection_fibration {E B : PointedSimplicialSet.{u}}
    (f : E ⟶ B) [KanComplex B.right] :
    Fibration (terminalPathHomotopyFiberProjection f).right :=
  _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedPullback_snd_fibration (terminalPathStart B) f

/-- Kan な源と標的の終点固定 homotopy fiber は Kan。 -/
instance terminalPathHomotopyFiber_kanComplex {E B : PointedSimplicialSet.{u}}
    (f : E ⟶ B) [KanComplex E.right] [KanComplex B.right] :
    KanComplex (terminalPathHomotopyFiber f).right :=
  _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedPullback_kanComplex (terminalPathStart B) f

/-- 元の loop と始点評価の基点 fiber の点つき同型。 -/
def loopPointedTerminalPathFiberIso (B : PointedSimplicialSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace B ≅ pointedFiber (terminalPathStart B) :=
  Under.isoMk (loopTerminalBasedPathFiberIso B)
    (by
      exact Under.w (pointedHomOfBasepoint (X := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace B)
        (Y := pointedFiber (terminalPathStart B)) (loopTerminalBasedPathFiberIso B).hom (by
          exact (loopTerminalBasedPathFiberIso_basepoint B).trans
            (PointedSimplicialSet.basepoint_ofVertex _ _).symm)))

/-- 元の円の loop から終点固定 homotopy fiber への点つき包含。 -/
def loopToTerminalPathHomotopyFiber {E B : PointedSimplicialSet.{u}} (f : E ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace B ⟶ terminalPathHomotopyFiber f :=
  (loopPointedTerminalPathFiberIso B).hom ≫
    (pointedPullbackFiberIso (terminalPathStart B) f).inv ≫
      pointedFiberι (terminalPathHomotopyFiberProjection f)

/-- loop の包含は元の全空間の基点上にある。 -/
lemma loopToTerminalPathHomotopyFiber_projection {E B : PointedSimplicialSet.{u}} (f : E ⟶ B) :
    loopToTerminalPathHomotopyFiber f ≫ terminalPathHomotopyFiberProjection f = 0 := by
  simp only [loopToTerminalPathHomotopyFiber, Category.assoc, pointedFiberι_comp, comp_zero]

/-- loop の包含の path 成分は元の二端点商による制限。 -/
lemma loopToTerminalPathHomotopyFiber_path {E B : PointedSimplicialSet.{u}} (f : E ⟶ B) :
    loopToTerminalPathHomotopyFiber f ≫ pullback.fst (terminalPathStart B) f =
      (loopToTerminalEndpointHomIso B).hom ≫
        _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (pointedCofiberProjection terminalIntervalStart.{u}) B := by
  have hc : (pointedPullbackFiberIso (terminalPathStart B) f).inv ≫
      pointedFiberι (terminalPathHomotopyFiberProjection f) ≫
        pullback.fst (terminalPathStart B) f = pointedFiberι (terminalPathStart B) := by
    change pointedPullbackFiberFrom (terminalPathStart B) f ≫
      pointedFiberι (pullback.snd (terminalPathStart B) f) ≫ _ = _
    rw [← Category.assoc, pointedPullbackFiberFrom_ι, pullback.lift_fst]
  change (loopPointedTerminalPathFiberIso B).hom ≫
    (pointedPullbackFiberIso (terminalPathStart B) f).inv ≫
      pointedFiberι (terminalPathHomotopyFiberProjection f) ≫ _ = _
  rw [hc]
  apply Under.UnderMorphism.ext
  exact loopTerminalBasedPathFiberIso_hom_ι B

/-- 可縮 Kan な全空間に対して loop の包含は全基点 π 同型。 -/
lemma loopToTerminalPathHomotopyFiber_piIsomorphism {E B : PointedSimplicialSet.{u}}
    (f : E ⟶ B) [KanComplex E.right] [KanComplex B.right] (hE : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan E.right) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (loopToTerminalPathHomotopyFiber f).right := by
  let a := (loopPointedTerminalPathFiberIso B).hom
  let b := (pointedPullbackFiberIso (terminalPathStart B) f).inv
  have ha : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism a.right :=
    kanPiIsomorphism_of_localized_isIso a.right (by infer_instance)
  have hb : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism b.right :=
    kanPiIsomorphism_of_localized_isIso b.right (by infer_instance)
  have hi : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (pointedFiberι (terminalPathHomotopyFiberProjection f)).right :=
    fiberInclusion_piIsomorphism_of_contractible_base
      (terminalPathHomotopyFiberProjection f).right hE (terminalPathHomotopyFiber f).basepoint
  exact ha.comp (hb.comp hi)

end SerrePositivity.KST.SConstruction
