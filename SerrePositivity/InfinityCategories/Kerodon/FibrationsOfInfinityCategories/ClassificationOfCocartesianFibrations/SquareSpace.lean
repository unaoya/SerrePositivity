module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorVertices

/-!
概要：transport representation の可換四角形を全次数の関手空間に束ねる。
方針：pointed space への後合成と底の射による前合成の引き戻しを取る。
規約：fiber の同値性は別の頂点条件として課す。
使われ方：Kerodon Lemma 5.6.8.10（Tag 02SK）、表現の選択空間とその制限。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：空間値の底の図式と pointed space への全空間の射の厳密な可換四角形。
方針：二つの射と可換性を構造に束ねる。
規約：このデータだけでは表現の fiber 同値条件を要求しない。
使われ方：Kerodon §5.6.8（Tag 02S9）、表現空間の頂点の周囲の図式。 -/
structure LeftTransportSquare {E B : SSet.{u + 1}} (p : E ⟶ B) where
  diagram : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}
  pointedMap : E ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PointedSpaceInfinity.{u}
  comm : pointedMap ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection = p ≫ diagram

/-- 概要：表現の可換四角形を取り出す。
方針：構成済みの pointed space への射と可換性を使う。
規約：実際の射を保ち、比較の存在命題に落とさない。
使われ方：Kerodon §5.6.8（Tag 02S9）、表現の頂点と図式の族の接続。 -/
noncomputable def LeftTransportRepresentation.toSquare {E B : SSet.{u + 1}}
    {p : E ⟶ B} [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (R : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation p) : LeftTransportSquare p :=
  ⟨R.diagram, R.pointedMap, R.pointedMap_projection⟩

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation export _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftTransportRepresentation (toSquare)


/-- 概要：transport の可換四角形全体の単体集合。
方針：二つの関手空間から全空間の空間値関手空間への射の引き戻しを取る。
規約：p の fibration 性や底の quasicategory 性は定義に不要。
使われ方：Kerodon Lemma 5.6.8.10（Tag 02SK） の周囲の関手空間 M の空間値版。 -/
noncomputable def transportSquareSpace {E B : SSet.{u + 1}} (p : E ⟶ B) : SSet.{u + 1} :=
  pullback ((ihom E).map _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection) ((pre p).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})

/-- 概要：可換四角形の族から底の分類図式の族を取り出す。
方針：引き戻しの第二射影を使う。
規約：全次数の射であり、頂点だけの作用ではない。
使われ方：Kerodon §5.6.8（Tag 02S9）、表現の底側のパラメーター。 -/
noncomputable def transportSquareDiagram {E B : SSet.{u + 1}} (p : E ⟶ B) :
    transportSquareSpace p ⟶ (ihom B).obj _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} :=
  pullback.snd _ _

/-- 概要：可換四角形の族から全空間の pointed space 値図式の族を取り出す。
方針：引き戻しの第一射影を使う。
規約：全次数の射。
使われ方：Kerodon §5.6.8（Tag 02S9）、表現の全空間側のパラメーター。 -/
noncomputable def transportSquarePointed {E B : SSet.{u + 1}} (p : E ⟶ B) :
    transportSquareSpace p ⟶ (ihom E).obj _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PointedSpaceInfinity.{u} :=
  pullback.fst _ _

/-- 概要：四角形の族の二つの射影は関手空間で厳密に可換。
方針：引き戻し条件を使う。
規約：高次のパラメーターを含めた単体集合の射の等式。
使われ方：Kerodon §5.6.8（Tag 02S9）、頂点と高次単体の可換性の回収。 -/
lemma transportSquareSpace_condition {E B : SSet.{u + 1}} (p : E ⟶ B) :
    transportSquarePointed p ≫ (ihom E).map _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection =
      transportSquareDiagram p ≫ (pre p).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} := pullback.condition

/-- 概要：可換四角形の族の底側への射影は left fibration。
方針：pointed space 射影の内部 Hom と底変換の閉性を使う。
規約：p の fibration 性も底の quasicategory 性も不要。
使われ方：Kerodon Lemma 5.6.8.10（Tag 02SK）、周囲の図式の族の相対充填。 -/
instance transportSquareDiagram_leftFibration {E B : SSet.{u + 1}} (p : E ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (transportSquareDiagram p) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrations.pullback_snd _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem (p := (ihom E).map _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection))⟩

/-- 概要：可換四角形全体は quasicategory。
方針：関手空間への left fibration の全空間の判定を使う。
規約：元の底 B の quasicategory 性を要求しない。
使われ方：Kerodon §5.6.8（Tag 02S9）、表現の全部分複体を定義する周囲の ∞ 圏。 -/
instance transportSquareSpace_quasicategory {E B : SSet.{u + 1}} (p : E ⟶ B) :
    Quasicategory (transportSquareSpace p) :=
  quasicategory_of_innerFibration (transportSquareDiagram p)

/-- 概要：底の図式を固定した可換四角形の空間は相対関手空間と同型。
方針：引き戻しの fiber 同型で第一射影側の fiber を回収する。
規約：元の分類図式 F を厳密に固定する。
使われ方：Kerodon §5.6.8（Tag 02S9）、既存の相対充填と可換四角形の空間の接続。 -/
noncomputable def transportSquareDiagramFiberIso {E B : SSet.{u + 1}}
    (p : E ⟶ B) (F : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (transportSquareDiagram p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection (p ≫ F) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.vertexFiberPullbackIso ((ihom E).map _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection) ((pre p).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity) _

/-- 概要：厳密な可換四角形をその関手空間の頂点へ写す。
方針：二つの関手頂点から引き戻しへの射を作り Yoneda で頂点に戻す。
規約：可換性は厳密な射の等式を使う。
使われ方：Kerodon §5.6.8（Tag 02S9）、表現データを全次数の空間へ埋め込む。 -/
noncomputable def transportSquareVertex {E B : SSet.{u + 1}} {p : E ⟶ B}
    (S : LeftTransportSquare p) : (transportSquareSpace p) _⦋0⦌ :=
  SSet.yonedaEquiv (pullback.lift (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex S.pointedMap))
    (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex S.diagram)) (by
      apply SSet.yonedaEquiv.injective
      change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (S.pointedMap ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (p ≫ S.diagram)
      rw [S.comm]))

/-- 概要：四角形の頂点の底成分は元の分類図式の頂点。
方針：Yoneda の自然性と引き戻しの第二射影の公式を使う。
規約：頂点の厳密な等式。
使われ方：Kerodon §5.6.8（Tag 02S9）、頂点対応の順方向の計算。 -/
lemma transportSquareVertex_diagram {E B : SSet.{u + 1}} {p : E ⟶ B}
    (S : LeftTransportSquare p) :
    (transportSquareDiagram p).app _ (transportSquareVertex S) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex S.diagram := by
  change SSet.yonedaEquiv (_ ≫ pullback.snd _ _) = _
  rw [pullback.lift_snd, Equiv.apply_symm_apply]

/-- 概要：四角形の頂点の全空間成分は元の pointed space 値図式の頂点。
方針：Yoneda の自然性と引き戻しの第一射影の公式を使う。
規約：頂点の厳密な等式。
使われ方：Kerodon §5.6.8（Tag 02S9）、全空間の射を保つ頂点対応。 -/
lemma transportSquareVertex_pointed {E B : SSet.{u + 1}} {p : E ⟶ B}
    (S : LeftTransportSquare p) :
    (transportSquarePointed p).app _ (transportSquareVertex S) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex S.pointedMap := by
  change SSet.yonedaEquiv (_ ≫ pullback.fst _ _) = _
  rw [pullback.lift_fst, Equiv.apply_symm_apply]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
