module
public import SerrePositivity.KST.SConstruction.TracedTripleGeometricStagePasting
public import SerrePositivity.KST.SConstruction.TracedTripleOuterBinaryFaces

/-! # 元の raw 各段の実消去から全十二面と共有円柱を回収する
概要：実結合替え四面体の指定面を元の全三角形へ厳密に照合する。
方針：一般的な全保存面の式と、元の各段の全面回収式を合成する。
規約：外側二部分面への全正規化移送も保持し、構造適合の代用にはしない。
使われ方：元の全高次 prism と全実消去の選択を同時に保持する相対構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet Spectra
open scoped Simplicial
variable {I : Type u} [SmallCategory I] (F : I ⥤ StableModel.{u})
  {w x y z : I} (f : w ⟶ x) (g : x ⟶ y) (h : y ⟶ z)

/-- 同じ実四面体の指定面に前二射の元の全面を厳密に保持する。 -/
lemma monicKTracedTripleGeometricStagePasting_first_stage (n : ℕ) :
    stdSimplex.δ 3 ≫
        SSet.yonedaEquiv.symm
          (monicKTracedTripleGeometricStagePasting F f g h n).secondMove.simplex =
      SSet.yonedaEquiv.symm (monicKTracedTripleFirstPairStageTriangle F f g h n).simplex :=
  (monicKTracedTripleGeometricStagePasting F f g h n).first_stage.trans
    (monicKTracedTripleFirstPairDiamond_stage F f g h n)

/-- 同じ実四面体の指定面に前二射の元の二部分全面を厳密に保持する。 -/
lemma monicKTracedTripleGeometricStagePasting_first_binary (n : ℕ) :
    stdSimplex.δ 3 ≫
        SSet.yonedaEquiv.symm
          (monicKTracedTripleGeometricStagePasting F f g h n).thirdMove.simplex =
      SSet.yonedaEquiv.symm (monicKTracedTripleFirstPairBinaryTriangle F f g h n).simplex :=
  (monicKTracedTripleGeometricStagePasting F f g h n).first_binary.trans
    (monicKTracedTripleFirstPairDiamond_binary F f g h n)

/-- 同じ実四面体の指定面に後二射の元の全面を厳密に保持する。 -/
lemma monicKTracedTripleGeometricStagePasting_last_stage (n : ℕ) :
    stdSimplex.δ 0 ≫
        SSet.yonedaEquiv.symm
          (monicKTracedTripleGeometricStagePasting F f g h n).fourthMove.simplex =
      SSet.yonedaEquiv.symm (monicKTracedTripleLastPairStageTriangle F f g h n).simplex :=
  (monicKTracedTripleGeometricStagePasting F f g h n).last_stage.trans
    (monicKTracedTripleLastPairDiamond_stage F f g h n)

/-- 同じ実四面体の指定面に後二射の元の二部分全面を厳密に保持する。 -/
lemma monicKTracedTripleGeometricStagePasting_last_binary (n : ℕ) :
    stdSimplex.δ 0 ≫
        SSet.yonedaEquiv.symm
          (monicKTracedTripleGeometricStagePasting F f g h n).thirdMove.simplex =
      SSet.yonedaEquiv.symm (monicKTracedTripleLastPairBinaryTriangle F f g h n).simplex :=
  (monicKTracedTripleGeometricStagePasting F f g h n).last_binary.trans
    (monicKTracedTripleLastPairDiamond_binary F f g h n)

/-- 同じ実四面体の指定面に元の交換第一全面を厳密に保持する。 -/
lemma monicKTracedTripleGeometricStagePasting_interchange_first (n : ℕ) :
    stdSimplex.δ 0 ≫
        SSet.yonedaEquiv.symm
          (monicKTracedTripleGeometricStagePasting F f g h n).firstMove.simplex =
      SSet.yonedaEquiv.symm (monicKTracedTripleInterchangeDiamond F f g h n).first.simplex :=
  (monicKTracedTripleGeometricStagePasting F f g h n).interchange_first

/-- 同じ実四面体の指定面に元の交換第二全面を厳密に保持する。 -/
lemma monicKTracedTripleGeometricStagePasting_interchange_second (n : ℕ) :
    stdSimplex.δ 0 ≫
        SSet.yonedaEquiv.symm
          (monicKTracedTripleGeometricStagePasting F f g h n).secondMove.simplex =
      SSet.yonedaEquiv.symm (monicKTracedTripleInterchangeDiamond F f g h n).second.simplex :=
  (monicKTracedTripleGeometricStagePasting F f g h n).interchange_second

/-- 同じ実四面体の指定面に元の右外側全段面を厳密に保持する。 -/
lemma monicKTracedTripleGeometricStagePasting_right_stage (n : ℕ) :
    stdSimplex.δ 3 ≫
        SSet.yonedaEquiv.symm
          (monicKTracedTripleGeometricStagePasting F f g h n).fifthMove.simplex =
      SSet.yonedaEquiv.symm
        (monicKTracedCompositionStageTriangleData F f (g ≫ h) n).triangle.simplex :=
  (monicKTracedTripleGeometricStagePasting F f g h n).right_stage.trans
    (monicKTracedTripleRightOuterDiamond_stage F f g h n)

/-- 同じ実四面体の指定面に元の第一 BF 全面の同じ raw 評価を厳密に保持する。 -/
lemma monicKTracedTripleGeometricStagePasting_bf_first (n : ℕ) :
    stdSimplex.δ 0 ≫
        SSet.yonedaEquiv.symm
          (monicKTracedTripleGeometricStagePasting F f g h n).fifthMove.simplex =
      monicKTracedTripleRawFirstTriangle F f g h n :=
  (monicKTracedTripleGeometricStagePasting F f g h n).bf_first.trans
    (monicKTracedTripleBFDiamond_first F f g h n)

/-- 同じ実四面体の指定面に元の第二 BF 全面の同じ raw 評価を厳密に保持する。 -/
lemma monicKTracedTripleGeometricStagePasting_bf_second (n : ℕ) :
    stdSimplex.δ 0 ≫
        SSet.yonedaEquiv.symm
          (monicKTracedTripleGeometricStagePasting F f g h n).sixthMove.simplex =
      monicKTracedTripleRawSecondTriangle F f g h n :=
  (monicKTracedTripleGeometricStagePasting F f g h n).bf_second.trans
    (monicKTracedTripleBFDiamond_second F f g h n)

/-- 同じ実四面体の指定面に左外側全面の同じ正規化移送を厳密に保持する。 -/
lemma monicKTracedTripleGeometricStagePasting_left_binary (n : ℕ) :
    stdSimplex.δ 3 ≫
        SSet.yonedaEquiv.symm
          (monicKTracedTripleGeometricStagePasting F f g h n).firstMove.simplex =
      SSet.yonedaEquiv.symm (monicKTracedTripleLeftBinaryTransport F f g h n).simplex :=
  (monicKTracedTripleGeometricStagePasting F f g h n).left_binary

/-- 同じ実四面体の指定面に右外側全面の同じ正規化移送を厳密に保持する。 -/
lemma monicKTracedTripleGeometricStagePasting_right_binary (n : ℕ) :
    stdSimplex.δ 3 ≫
        SSet.yonedaEquiv.symm
          (monicKTracedTripleGeometricStagePasting F f g h n).fourthMove.simplex =
      SSet.yonedaEquiv.symm (monicKTracedTripleRightBinaryTransport F f g h n).simplex :=
  (monicKTracedTripleGeometricStagePasting F f g h n).right_binary

/-- 元の左外側全段面は、同じ全三辺移送の始端そのもの。 -/
lemma monicKTracedTripleGeometricStagePasting_left_stage (n : ℕ) :
    SSet.ι₀ ≫ (monicKTracedTripleGeometricStagePasting F f g h n).transportComparison.h =
      SSet.yonedaEquiv.symm
        (monicKTracedCompositionStageTriangleData F (f ≫ g) h n).triangle.simplex :=
  (monicKTracedTripleGeometricStagePasting F f g h n).left_stage.trans
    (monicKTracedTripleLeftOuterDiamond_stage F f g h n)

/-- 元の共有直接全円柱も、同じ全三辺移送の下面として厳密に保持する。 -/
lemma monicKTracedTripleGeometricStagePasting_shared_direct (n : ℕ) :
    (stdSimplex.δ 2 ▷ (Δ[1] : SSet.{u})) ≫
        (monicKTracedTripleGeometricStagePasting F f g h n).transportComparison.h =
      (monicKTracedTripleDirectComparison F f g h n).h :=
  (monicKTracedTripleGeometricStagePasting F f g h n).shared_direct.trans
    (monicKTracedTripleTypedDirectComparison_h F f g h n)

end SerrePositivity.KST.SConstruction
