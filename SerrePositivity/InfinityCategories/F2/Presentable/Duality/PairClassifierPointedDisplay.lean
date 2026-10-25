module

public import SerrePositivity.InfinityCategories.F2.Presentable.Duality.PairAdjointFunctorMeaning
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.SmallLeftUnstraighteningOverMap
public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftFibrationFiberReflection
public import SerrePositivity.InfinityCategories.F1.Transport.ParametrizedPointTransportSquare

/-!
概要：元の left fibration の分類に沿う pointed-space への実際の全空間比較。
方針：元の復元射を小さい unstraightening の厳密な同型へ続け、各 fiber の同値を保つ。
規約：元の全空間と分類図式を固定する。一般の Cartesian 分類は追加しない。
使われ方：単位族の指定点での評価と元の関手の Hom 作用の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Duality
attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- 概要：元の left fibration の全空間を同じ分類図式上の pointed-space へ送る。
方針：同じ復元射の後に縮小同型と普遍引き戻しの第一脚を続ける。
規約：元の単位を点として保持するための同じ一つの単体写像。
使われ方：元の単位輸送と分類の値の輸送の比較。 -/
def pairClassifierPointedDisplay {E B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) [LeftFibration p] :
    (SSet.uliftFunctor.{u + 1, u}).obj E ⟶ PointedSpaceInfinity.{u} :=
  (SSet.uliftFunctor.{u + 1, u}).map (leftStraighteningInfinityReconstruction p) ≫
    (smallLeftUnstraighteningIso (leftStraighteningInfinityDiagram p)).hom ≫
      pullback.fst pointedSpaceProjection (leftStraighteningInfinityDiagram p)

/-- 概要：同じ全空間比較は元の射影と同じ分類図式の上にある。
方針：復元射の底の式と小さい unstraightening の同型の底の式を使う。
規約：元の底を別の表示に置き換えない。
使われ方：輸送の自然性の可換正方形。 -/
lemma pairClassifierPointedDisplay_projection {E B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) [LeftFibration p] :
    pairClassifierPointedDisplay p ≫ pointedSpaceProjection =
      (SSet.uliftFunctor.{u + 1, u}).map p ≫ leftStraighteningInfinityDiagram p := by
  rw [pairClassifierPointedDisplay, Category.assoc, Category.assoc, pullback.condition]
  change (SSet.uliftFunctor.map _) ≫
    (smallLeftUnstraighteningIso (leftStraighteningInfinityDiagram p)).hom ≫
      leftUnstraighteningProjection (leftStraighteningInfinityDiagram p) ≫ _ = _
  rw [← Category.assoc (smallLeftUnstraighteningIso _).hom,
    smallLeftUnstraighteningIso_projection, ← CategoryTheory.Functor.map_comp_assoc]
  exact congrArg (fun f ↦ (SSet.uliftFunctor.{u + 1, u}).map f ≫
    leftStraighteningInfinityDiagram p) (leftStraighteningInfinityReconstruction_projection p)

/-- 概要：同じ全空間比較の元の頂点 fiber への作用。
方針：元の可換正方形の標準 fiber 写像を取る。
規約：元の全空間比較自体の作用。
使われ方：指定点輸送の同値性を元の単位空間から分類の値へ送る。 -/
def pairClassifierPointedDisplayFiber {E B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) [LeftFibration p] (b : B _⦋0⦌) :
    vertexFiber ((SSet.uliftFunctor.{u + 1, u}).map p) (ULift.up b) ⟶
      vertexFiber pointedSpaceProjection
        ((leftStraighteningInfinityDiagram p).app (Opposite.op ⦋0⦌) (ULift.up b)) :=
  transportSquareFiberMap ((SSet.uliftFunctor.{u + 1, u}).map p)
    pointedSpaceProjection (pairClassifierPointedDisplay p) (leftStraighteningInfinityDiagram p)
    (pairClassifierPointedDisplay_projection p) (ULift.up b)

/-- 概要：元の fiber 作用は復元の作用と三つの厳密な fiber 同型の合成。
方針：全空間への包含後で各段階の同じ作用を比較する。
規約：復元射を元の射のまま保持する。
使われ方：元の分類正方形の fiber 同値性。 -/
lemma pairClassifierPointedDisplayFiber_compare {E B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) [LeftFibration p] (b : B _⦋0⦌) :
    pairClassifierPointedDisplayFiber p b =
      (uliftVertexFiberIso.{u, u + 1} p b).inv ≫
        (SSet.uliftFunctor.{u + 1, u}).map
          (vertexFiberMap p (smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram p))
            (leftStraighteningInfinityReconstruction p)
            (leftStraighteningInfinityReconstruction_projection p) b) ≫
        (smallLeftUnstraighteningFiberIso (leftStraighteningInfinityDiagram p) b).hom ≫
        (leftUnstraighteningFiberIso (leftStraighteningInfinityDiagram p) (ULift.up b)).hom := by
  apply vertexFiber_hom_ext pointedSpaceProjection
    ((leftStraighteningInfinityDiagram p).app (Opposite.op ⦋0⦌) (ULift.up b))
  simp only [pairClassifierPointedDisplayFiber, Category.assoc]
  rw [transportSquareFiberMap_ι, leftUnstraighteningFiberIso_hom_ι]
  rw [← Category.assoc (smallLeftUnstraighteningFiberIso _ _).hom,
    smallLeftUnstraighteningFiberIso_hom_ι]
  simp only [Category.assoc]
  rw [← CategoryTheory.Functor.map_comp_assoc, vertexFiberMap_ι, CategoryTheory.Functor.map_comp]
  have h := congrArg (fun f ↦ f ≫
    (SSet.uliftFunctor.{u + 1, u}).map (leftStraighteningInfinityReconstruction p) ≫
    (smallLeftUnstraighteningIso (leftStraighteningInfinityDiagram p)).hom ≫
    pullback.fst pointedSpaceProjection (leftStraighteningInfinityDiagram p))
    (uliftVertexFiberIso_inv_ι.{u, u + 1} p b)
  simpa only [pairClassifierPointedDisplay, Category.assoc] using h.symm

/-- 概要：同じ全空間比較の実際の fiber 作用は全ての元の頂点で同値。
方針：復元の fiber 同値と宇宙・引き戻しの厳密な同型を合成する。
規約：元の作用を別の同値で置き換えない。
使われ方：単位での評価を保つ輸送の同値性の比較。 -/
lemma pairClassifierPointedDisplayFiber_isQCatEquivalence {E B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) [LeftFibration p] (b : B _⦋0⦌) :
    IsQCatEquivalence (pairClassifierPointedDisplayFiber p b) := by
  rw [pairClassifierPointedDisplayFiber_compare]
  have h₁ := (qCatEquivalenceOfIso (uliftVertexFiberIso.{u, u + 1} p b).symm).isQCatEquivalence
  have h₂ := (vertexFiberMap_isQCatEquivalence_of_precompositionEquivalence p
    (smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram p))
    (leftStraighteningInfinityReconstruction p) (leftStraighteningInfinityReconstruction_projection p)
    (leftStraighteningInfinityReconstruction_isPrecompositionEquivalence p) b).ulift.{u, u + 1}
  have h₃ := (qCatEquivalenceOfIso
    (smallLeftUnstraighteningFiberIso (leftStraighteningInfinityDiagram p) b)).isQCatEquivalence
  have h₄ := (qCatEquivalenceOfIso
    (leftUnstraighteningFiberIso (leftStraighteningInfinityDiagram p) (ULift.up b))).isQCatEquivalence
  exact h₁.comp (h₂.comp (h₃.comp h₄))

end SerrePositivity.InfinityCategories.F2.Presentable.Duality
