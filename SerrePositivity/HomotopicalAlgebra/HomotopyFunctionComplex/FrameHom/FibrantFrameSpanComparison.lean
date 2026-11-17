module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FibrantRightResolutionDiagram
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.HeterogeneousSmallComma
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.AnodyneWeakDetection

/-!
概要：fibrant な元の標的で source frame の全単体を全三本矢へ弱比較する。
方針：同じ固定 fiber、全解像図式、全左脚図式、元の三本矢の回収を合成する。
規約：全単体と元の射を保ち、全対象 fibrant の仮定を加えない。
使われ方：bifibrant 中継での実 frame と hammock の比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FibrantFrameSpanComparison
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomotopicalAlgebra _root_.Opposite
open _root_.SerrePositivity.Reedy _root_.SerrePositivity.HomotopyFunctionComplex
open _root_.SerrePositivity.SimplicialModel _root_.SerrePositivity.InfinityCategories
open _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FibrantRightResolutionDiagram
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {X : C} (q : CofibrantResolution (C := C) simplex X) (Y : C) [IsFibrant Y]

/-- 概要：元の全単体を同じ恒等右脚の固定 fiber へ送る。
方針：元の Hom の全単体と同じ comma の明示的な同値を使う。
規約：元の射と次数を保つ。使われ方：全図式への元の実包含。 -/
def fiberNerveMap : nerve (AsSmall.{max u v} ((((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom q.obj).obj Y).Elements)ᵒᵖ)) ⟶
    nerve ((_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FibrantRightResolutionDiagram.resolutionDiagram q Y).obj (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FibrantRightResolutionDiagram.smallInitial Y)) :=
  nerveMap (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CosimplicialHomElements.smallEquivalence.{u, v, max u v} q.obj Y).functor

/-- 概要：同じ固定 fiber の比較は anodyne 反転後に可逆。
方針：明示的な圏同値の同じ順射を使う。
規約：元の全射を保つ。使われ方：全図式への弱比較の始域。 -/
lemma fiberNerveMap_localized_isIso :
    IsIso (AnodyneHomotopy.anodyneQ.map (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FibrantFrameSpanComparison.fiberNerveMap q Y)) :=
  (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveEquivalenceImage.imageIso
    (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CosimplicialHomElements.smallEquivalence.{u, v, max u v} q.obj Y)
    AnodyneHomotopy.anodyneQ (Localization.inverts _ SSet.anodyneExtensions)).isIso_hom

/-- 概要：元の全単体を同じ全解像図式へ送る。
方針：元の固定 fiber の比較と同じ実 fiber 包含を合成する。
規約：同じ恒等右脚を使う。使われ方：全左脚との実比較。 -/
def resolutionNerveMap :
    nerve (AsSmall.{max u v} ((((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom q.obj).obj Y).Elements)ᵒᵖ)) ⟶
      nerve (Grothendieck (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FibrantRightResolutionDiagram.resolutionDiagram q Y)) :=
  _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FibrantFrameSpanComparison.fiberNerveMap q Y ≫ (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.Thomason.selfLiftIso _).inv ≫
    _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.Thomason.fiberNerveMap (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FibrantRightResolutionDiagram.resolutionDiagram q Y) (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FibrantRightResolutionDiagram.smallInitial Y)

/-- 概要：同じ全解像図式への射は anodyne 反転後に可逆。
方針：元の fixed fiber と全不変図式の包含の反転性を合成する。
規約：元の比較射自身。使われ方：全三本矢への弱比較。 -/
lemma resolutionNerveMap_localized_isIso :
    IsIso (AnodyneHomotopy.anodyneQ.map (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FibrantFrameSpanComparison.resolutionNerveMap q Y)) := by
  have := _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FibrantFrameSpanComparison.fiberNerveMap_localized_isIso q Y
  have := _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FibrantRightResolutionDiagram.fiberNerveMap_localized_isIso q Y (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FibrantRightResolutionDiagram.smallInitial Y)
  dsimp only [_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FibrantFrameSpanComparison.resolutionNerveMap]
  rw [Functor.map_comp, Functor.map_comp]
  infer_instance

/-- 概要：元の全単体を同じ全左脚・全右脚の図式へ送る。
方針：元の全解像図式の後に同じ Grothendieck 比較を置く。
規約：元の中間射を保つ。使われ方：元の三本矢への実回収。 -/
def spanDiagramNerveMap :
    nerve (AsSmall.{max u v} ((((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom q.obj).obj Y).Elements)ᵒᵖ)) ⟶
      nerve (Grothendieck (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FibrantRightResolutionDiagram.spanDiagram (X := X) Y)) :=
  _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FibrantFrameSpanComparison.resolutionNerveMap q Y ≫ nerveMap (Grothendieck.map (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FibrantRightResolutionDiagram.comparison q Y))

/-- 概要：同じ全左脚図式への元の比較は anodyne 反転後に可逆。
方針：元の解像側と全図式比較の反転性を合成する。
規約：同じ元の比較。使われ方：全三本矢への弱比較。 -/
lemma spanDiagramNerveMap_localized_isIso :
    IsIso (AnodyneHomotopy.anodyneQ.map (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FibrantFrameSpanComparison.spanDiagramNerveMap q Y)) := by
  have := _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FibrantFrameSpanComparison.resolutionNerveMap_localized_isIso q Y
  have := _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FibrantRightResolutionDiagram.comparison_localized_isIso q Y
  dsimp only [_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FibrantFrameSpanComparison.spanDiagramNerveMap]
  rw [Functor.map_comp]
  infer_instance

/-- 概要：全左脚図式から元の fibrant 三本矢への実回収。
方針：異なる宇宙の同じ comma を down し、元の三射を取り出す。
規約：元の両端点と中間射を保持。使われ方：元の frame 比較の照合。 -/
def recoveryNerveMap : nerve (Grothendieck (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FibrantRightResolutionDiagram.spanDiagram (X := X) Y)) ⟶
    nerve (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.FibrantRightSpans.FibrantSpan X Y) :=
  _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.HeterogeneousSmallComma.recoveryNerveMap.{max u v, v, max u v, v, u, v, max u v}
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ArrowSpanComma.leftSliceForget (trivialFibrations C) X) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.forget Y) ≫
      (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.Thomason.selfLiftIso _).hom ≫ nerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.fromComma X Y)

omit [IsFibrant Y] in
/-- 概要：同じ元の三本矢への回収は anodyne 反転後に可逆。
方針：同じ宇宙比較と明示的な両脚表示の同値を使う。
規約：元の回収射自身。使われ方：frame の比較射の弱同値性。 -/
lemma recoveryNerveMap_localized_isIso :
    IsIso (AnodyneHomotopy.anodyneQ.map (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FibrantFrameSpanComparison.recoveryNerveMap (X := X) Y)) := by
  have := _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.HeterogeneousSmallComma.recoveryNerveMap_localized_isIso
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ArrowSpanComma.leftSliceForget (trivialFibrations C) X) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.forget Y)
  have : IsIso (AnodyneHomotopy.anodyneQ.map
      (nerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.fromComma X Y))) :=
    (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveEquivalenceImage.imageIso (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.commaEquivalence X Y).symm
      AnodyneHomotopy.anodyneQ (Localization.inverts _ SSet.anodyneExtensions)).isIso_hom
  dsimp only [_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FibrantFrameSpanComparison.recoveryNerveMap]
  rw [Functor.map_comp, Functor.map_comp]
  infer_instance

/-- 概要：元の全単体から元の fibrant 三本矢への実比較。
方針：同じ全図式への比較と元の三射の回収を合成する。
規約：元の全単体と全作用素。使われ方：実 hammock の写像空間への比較。 -/
def fibrantSpanNerveMap :
    nerve (AsSmall.{max u v} ((((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom q.obj).obj Y).Elements)ᵒᵖ)) ⟶
      nerve (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.FibrantRightSpans.FibrantSpan X Y) :=
  _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FibrantFrameSpanComparison.spanDiagramNerveMap q Y ≫ _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FibrantFrameSpanComparison.recoveryNerveMap Y

/-- 概要：同じ元の frame 比較は弱ホモトピー同値。
方針：各実比較射の反転性を同じ anodyne 局所化で合成する。
規約：元の標的の fibrancy のみを要求。使われ方：一般モデルの frame 比較。 -/
lemma fibrantSpanNerveMap_isWeakHomotopyEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FibrantFrameSpanComparison.fibrantSpanNerveMap q Y) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.AnodyneWeakDetection.isWeakHomotopyEquivalence
  have := _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FibrantFrameSpanComparison.spanDiagramNerveMap_localized_isIso q Y
  have := _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FibrantFrameSpanComparison.recoveryNerveMap_localized_isIso (X := X) Y
  dsimp only [_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FibrantFrameSpanComparison.fibrantSpanNerveMap]
  rw [Functor.map_comp]
  infer_instance

end SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FibrantFrameSpanComparison
