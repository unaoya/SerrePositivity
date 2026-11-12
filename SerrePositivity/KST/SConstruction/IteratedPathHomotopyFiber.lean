module
public import SerrePositivity.KST.SConstruction.PathHomotopyFiberFunctor
public import SerrePositivity.KST.SConstruction.PointedFullPathBoundary

/-! # 反復経路境界の homotopy fiber と loop の自然な比較
概要：既存の全零境界商の Kan 模型への反復経路境界の homotopy fiber を構成する。
方針：可縮 Kan な経路全空間と、一般の path homotopy fiber の比較を使う。
規約：この比較だけで反復 S の Ω 条件とはしない。使われ方：残る fiber–反復実現比較の標的。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open Spectra

/-- 概要：点つき反復経路境界の path homotopy fiber。
方針：既存の Kan 境界に基点からの path の引き戻しを適用する。
規約：標的は既存の全零境界商の Kan 模型。使われ方：反復 S の fiber 比較。 -/
def iteratedPathHomotopyFiber (r : ℕ) (X : StableModel.{u}) : PointedSimplicialSet.{u} :=
  pathHomotopyFiber (pointedFullIteratedPathKanBoundary r X)

/-- 概要：反復経路境界の homotopy fiber は Kan。
方針：境界の源と標的の既存の Kan 性を使う。
規約：境界射そのものの fibration 性は要求しない。使われ方：実際の π_* の比較。 -/
instance iteratedPathHomotopyFiber_kanComplex (r : ℕ) (X : StableModel.{u}) :
    KanComplex (iteratedPathHomotopyFiber r X).right :=
  pathHomotopyFiber_kanComplex (pointedFullIteratedPathKanBoundary r X)

/-- 概要：入力の射が反復経路境界の homotopy fiber に誘導する点つき射。
方針：境界の厳密な自然性の正方形を引き戻しへ移す。
規約：安定な入力の全射に定義。使われ方：homotopy fiber の関手性。 -/
def iteratedPathHomotopyFiberMap (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    iteratedPathHomotopyFiber r X ⟶ iteratedPathHomotopyFiber r Y :=
  pathHomotopyFiberMap (pointedFullIteratedPathKanBoundary r X)
    (pointedFullIteratedPathKanBoundary r Y) ((pointedIteratedPathKanFunctor r).map f)
    ((boundaryKanRealizationFunctor r).map f)
    ((pointedFullIteratedPathKanBoundaryNat r).naturality f).symm

/-- 概要：反復経路境界の homotopy fiber の入力についての関手。
方針：可換正方形の引き戻しの恒等・合成法則を使う。
規約：選択を含まない厳密な関手。使われ方：自然な fiber–loop 比較。 -/
def iteratedPathHomotopyFiberFunctor (r : ℕ) : StableModel.{u} ⥤ PointedSimplicialSet.{u} :=
  pathHomotopyFiberFunctorOfNat (pointedFullIteratedPathKanBoundaryNat r)

/-- 概要：既存の Kan な反復実現の loop から経路境界の homotopy fiber への比較。
方針：基点上の path を引き戻しの基点 fiber として含める。
規約：実際の点つき写像。使われ方：delooping の fiber 比較の一方。 -/
def iteratedPathLoopComparison (r : ℕ) (X : StableModel.{u}) :
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace ((boundaryKanRealizationFunctor r).obj X) ⟶ iteratedPathHomotopyFiber r X :=
  loopToPathHomotopyFiber (pointedFullIteratedPathKanBoundary r X)

/-- 概要：反復経路境界の homotopy fiber と標的の loop の比較は全基点 π_* 同型。
方針：反復経路の実際の可縮 Kan 性に一般の比較を適用する。
規約：全自然数次数を含み、追加仮定はない。使われ方：残る反復 S 実現との比較。 -/
lemma iteratedPathLoopComparison_piIsomorphism (r : ℕ) (X : StableModel.{u}) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (iteratedPathLoopComparison r X).right :=
  loopToPathHomotopyFiber_piIsomorphism (pointedFullIteratedPathKanBoundary r X)
    (pointedIteratedPathKan_isContractibleKan r X)

/-- 概要：loop と反復経路の homotopy fiber の自然な比較。
方針：path homotopy fiber と loop の包含の正方形についての自然性を使う。
規約：安定な入力の射について厳密に自然。使われ方：連結 K の delooping の自然性。 -/
def iteratedPathLoopComparisonNat (r : ℕ) :
    boundaryKanRealizationFunctor.{u} r ⋙
      PointedObject.basedHomFunctor PointedSimplicialSet.circle ⟶
      iteratedPathHomotopyFiberFunctor r :=
  loopToPathHomotopyFiberNat (pointedFullIteratedPathKanBoundaryNat r)

end SerrePositivity.KST.SConstruction
