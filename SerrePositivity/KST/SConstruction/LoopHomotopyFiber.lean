module
public import SerrePositivity.KST.SConstruction.PointedPullbackFiber
public import SerrePositivity.KST.SConstruction.FiberOverContractibleBase
public import SerrePositivity.KST.Spectra.LoopPathFiber

/-! # 可縮な全空間を持つ点つき射の homotopy fiber と loop
概要：基点からの path を引き戻す homotopy fiber に、標的の loop を点つきに含める。
方針：引き戻しの基点 fiber を loop に同定し、可縮な底の fiber 包含の π_* 同型を使う。
規約：元の射の fibration 性は要求しない。使われ方：反復経路境界の homotopy fiber の比較。
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
open scoped Simplicial

/-- 概要：点つき射の標的の基点から始まる path による homotopy fiber 模型。
方針：path の終点評価を元の射に沿って引き戻す。
規約：path の始点は標的の基点。使われ方：経路境界の homotopy fiber。 -/
def pathHomotopyFiber {E B : PointedSimplicialSet.{u}} (f : E ⟶ B) :
    PointedSimplicialSet.{u} := pullback (pathEndpoint B) f

/-- 概要：path による homotopy fiber の元の全空間への射影。
方針：引き戻しの第二射影を取る。
規約：この射の基点 fiber が標的の loop になる。使われ方：可縮な底の fiber 比較。 -/
def pathHomotopyFiberProjection {E B : PointedSimplicialSet.{u}} (f : E ⟶ B) :
    pathHomotopyFiber f ⟶ E := pullback.snd (pathEndpoint B) f

/-- 概要：Kan 標的の path homotopy fiber の射影は Kan fibration。
方針：終点評価の Kan fibration 性を引き戻す。
規約：元の源 E の Kan 性は不要。使われ方：fiber の Kan 性。 -/
instance pathHomotopyFiberProjection_fibration {E B : PointedSimplicialSet.{u}}
    (f : E ⟶ B) [KanComplex B.right] : Fibration (pathHomotopyFiberProjection f).right :=
  _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedPullback_snd_fibration (pathEndpoint B) f

/-- 概要：Kan な点つき射の path homotopy fiber は Kan。
方針：Kan な源への Kan fibration の引き戻しを使う。
規約：元の射自体の fibration 性は不要。使われ方：実際の π_* の比較。 -/
instance pathHomotopyFiber_kanComplex {E B : PointedSimplicialSet.{u}}
    (f : E ⟶ B) [KanComplex E.right] [KanComplex B.right] :
    KanComplex (pathHomotopyFiber f).right := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedPullback_kanComplex (pathEndpoint B) f

/-- 概要：L9 の loop と path 終点評価の fiber の同型を点つき同型に束ねる。
方針：既存の底の同型の基点保存式を使う。
規約：標的の Kan 性は不要。使われ方：homotopy fiber の基点 fiber の同定。 -/
def loopPointedPathFiberIso (B : PointedSimplicialSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace B ≅ pointedFiber (pathEndpoint B) :=
  Under.isoMk (loopBasedPathFiberIso B)
    (by
      exact Under.w (pointedHomOfBasepoint (X := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace B)
        (Y := pointedFiber (pathEndpoint B)) (loopBasedPathFiberIso B).hom (by
          exact (loopBasedPathFiberIso_basepoint B).trans
            (PointedSimplicialSet.basepoint_ofVertex _ _).symm)))

/-- 概要：標的の loop から path homotopy fiber への点つき写像。
方針：loop を引き戻し射影の基点 fiber に同定して全空間へ含める。
規約：追加の収縮や nullhomotopy の選択を含まない。使われ方：反復経路境界の loop 比較。 -/
def loopToPathHomotopyFiber {E B : PointedSimplicialSet.{u}} (f : E ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace B ⟶ pathHomotopyFiber f :=
  (loopPointedPathFiberIso B).hom ≫ (pointedPullbackFiberIso (pathEndpoint B) f).inv ≫
    pointedFiberι (pathHomotopyFiberProjection f)

/-- 概要：loop の homotopy fiber への像は元の全空間の基点上にある。
方針：基点 fiber の包含の零合成を使う。
規約：点つき射の厳密な零合成。使われ方：標準の loop 部分の回収。 -/
lemma loopToPathHomotopyFiber_projection {E B : PointedSimplicialSet.{u}} (f : E ⟶ B) :
    loopToPathHomotopyFiber f ≫ pathHomotopyFiberProjection f = 0 := by
  simp only [loopToPathHomotopyFiber, Category.assoc, pointedFiberι_comp, comp_zero]

/-- 概要：源が可縮 Kan のとき標的の loop から homotopy fiber への射は全基点 π_* 同型。
方針：二つの実際の同型と、可縮な底の fiber 包含の π_* 同型を合成する。
規約：零次数を含み、元の射の fibration 性は不要。使われ方：反復経路境界の loop 比較。 -/
lemma loopToPathHomotopyFiber_piIsomorphism {E B : PointedSimplicialSet.{u}}
    (f : E ⟶ B) [KanComplex E.right] [KanComplex B.right] (hE : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan E.right) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (loopToPathHomotopyFiber f).right := by
  let a := (loopPointedPathFiberIso B).hom
  let b := (pointedPullbackFiberIso (pathEndpoint B) f).inv
  have ha : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism a.right :=
    kanPiIsomorphism_of_localized_isIso a.right (by infer_instance)
  have hb : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism b.right :=
    kanPiIsomorphism_of_localized_isIso b.right (by infer_instance)
  have hi : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (pointedFiberι (pathHomotopyFiberProjection f)).right :=
    fiberInclusion_piIsomorphism_of_contractible_base (pathHomotopyFiberProjection f).right hE
      (pathHomotopyFiber f).basepoint
  exact ha.comp (hb.comp hi)

end SerrePositivity.KST.SConstruction
