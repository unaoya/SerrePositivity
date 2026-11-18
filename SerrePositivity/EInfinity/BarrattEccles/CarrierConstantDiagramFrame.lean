module

public import SerrePositivity.EInfinity.BarrattEccles.CarrierConstantDiagramReplacement
public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.PointwiseTensorFrame

/-!
# 定値 複体図式の具体的な余単体的 frame

概要：BM 命題 4.1・Hovey §5.4 の定値図式置換を全次元の frame へ拡張する。
方針：同じ始域 frame の実現を、標準単体をテンソルした一点重みで評価する。
規約：モデル構造と生成分解は具体的に選び、元の複体の cofibrancy は不要。
使われ方：定値図式からの導来 Hom の重み付き錐表示。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram

open CategoryTheory Limits _root_.HomotopicalAlgebra
open SerrePositivity.DifferentialGraded
open SerrePositivity.Reedy SerrePositivity.HomotopyFunctionComplex
open SerrePositivity.DiagramModel

variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]

local instance : HasColimitsOfSize.{u, u} (Complex A) := ⟨fun _ _ => inferInstance⟩

local instance : HasColimitsOfSize.{0, u} (Complex A) :=
  hasColimitsOfSizeShrink.{0, u} _

/-- 概要：射影図式の自明 fibration は各値で自明 fibration（BM §1、Hovey §5）。
方針：具体的な図式モデルの二つの右類を評価で判定する。
規約：図式と複体のモデルを局所的に選ぶ。
使われ方：図式の frame の境界持ち上げ。 -/
lemma trivialFibration_app :
    let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
    let := projectiveModelCategory A K
    ∀ {F G : K ⥤ (Complex A)} (p : F ⟶ G),
      trivialFibrations (K ⥤ (Complex A)) p →
      ∀ k, trivialFibrations (Complex A) (p.app k) := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  let := projectiveModelCategory A K
  dsimp only
  intro F G p hp k
  exact ⟨(fibration_iff A K p).mp ⟨hp.1⟩ k,
    (weakEquivalence_iff A K p).mp ⟨hp.2⟩ k⟩

/-- 概要：射影図式の fibration は各値で fibration（BM §1、Hovey §5）。
方針：具体的な右類を各値の全次数全射性で判定する。
規約：全射は元の複体の同じ複体射で判定する。
使われ方：図式の frame のホーン持ち上げ。 -/
lemma fibration_app :
    let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
    let := projectiveModelCategory A K
    ∀ {F G : K ⥤ (Complex A)} (p : F ⟶ G),
      Fibration p → ∀ k, Fibration (p.app k) := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  let := projectiveModelCategory A K
  dsimp only
  intro F G p hp k
  exact ⟨(fibration_iff A K p).mp hp k⟩

/-- 概要：定値図式の frame を元の複体に関手的に構成する（Hovey §5.4）。
方針：始域 frame 族と各値の実現をテンソルした標準単体で評価する。
規約：全射と合成を保持する実際の関手。
使われ方：定値図式の導来 Hom の二変数の比較。 -/
def constantDiagramFrameFamily :
    (Complex A) ⥤ SimplexCategory ⥤ K ⥤ (Complex A) := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  exact (cosimplicialResolutionFamily (carrierProbeFactorization A)).obj ⋙
    Realization.family ⋙ Functor.whiskeringRight K SSet.{u} (Complex A) ⋙
      (Functor.whiskeringLeft SimplexCategory (K ⥤ SSet.{u}) (K ⥤ (Complex A))).obj
        (SSet.stdSimplex ⋙ WeightedCones.tensorDiagram K (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K))

/-- 概要：指定した 複体の定値図式の実際の frame（Hovey §5.4）。
方針：構成した関手族をその複体で評価する。
規約：全次元で同じ射影重みと始域 frame を使う。
使われ方：図式圏の局所化 Hom の計算。 -/
abbrev constantDiagramFrame (Y : (Complex A)) :
    SimplexCategory ⥤ K ⥤ (Complex A) := (constantDiagramFrameFamily A K).obj Y

/-- 概要：始域 frame の Hom 図式の重み付き錐（Hovey §5.4）。
方針：各値の始域 Hom と錐の実際の右随伴を合成する。
規約：元の複体に cofibrancy を仮定しない。
使われ方：定値図式からの導来 Hom と右 frame の錐の比較。 -/
def constantDiagramSourceHom (Y : (Complex A)) :
    (K ⥤ (Complex A)) ⥤ SSet.{u} := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  exact _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.pointwiseWeightedHom K (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K)
    ((cosimplicialResolutionFamily (carrierProbeFactorization A)).obj.obj Y)

/-- 概要：図式の frame の Hom は元の始域 frame の錐と同型（Hovey §5.4）。
方針：各値のテンソル実現の随伴と Yoneda 同型を使う。
規約：全単体と終域図式の射に自然。
使われ方：図式の局所化 Hom の重み付き錐表示。 -/
def constantDiagramFrameHomIso (Y : (Complex A)) :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (constantDiagramFrame A K Y) ≅ constantDiagramSourceHom A K Y := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  exact _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.pointwiseTensorFrameHomIso K (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K)
    ((cosimplicialResolutionFamily (carrierProbeFactorization A)).obj.obj Y)

/-- 概要：図式 frame の零次は構成済みの定値図式置換（Hovey §5.4）。
方針：零単体のテンソル単位同型を各値の実現で送る。
規約：既存の同じ置換図式へ比較する。
使われ方：局所化 Hom の始域の同定。 -/
def constantDiagramFrameZeroIso (Y : (Complex A)) :
    (constantDiagramFrame A K Y).obj (SimplexCategory.mk 0) ≅
      (constantDiagramReplacement A K).obj Y := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  exact _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.pointwiseTensorFrameZeroIso K (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K)
    ((cosimplicialResolutionFamily (carrierProbeFactorization A)).obj.obj Y)

/-- 概要：定値図式の frame は実際の射影図式モデルで Reedy cofibrant（Hovey §5.4）。
方針：重みの射影 cofibrancy と図式の自明 fibration の評価判定を使う。
規約：元の複体の cofibrancy は不要。
使われ方：図式の導来 Hom の π₀ 比較。 -/
lemma constantDiagramFrame_reedyCofibrant (Y : (Complex A)) :
    let := projectiveModelCategory A K
    reedyLeft simplex (cofibrations (K ⥤ (Complex A)))
      (initial.to (constantDiagramFrame A K Y)) := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  let := projectiveModelCategory A K
  let q := cosimplicialResolutionFamily (carrierProbeFactorization A)
  exact _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.pointwiseTensorFrame_reedyCofibrant K (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K)
    (q.obj.obj Y) (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight_cofibrant K) (q.cofibrant Y)
    (trivialFibration_app A K)

/-- 概要：定値図式 frame の全単体作用素は図式の弱同値（Hovey §5.4）。
方針：始域 frame の constancy と図式の fibration の評価判定を使う。
規約：図式圏のモデルを局所的に選ぶ。
使われ方：定値図式からの射の連結成分による計算。 -/
lemma constantDiagramFrame_homotopicallyConstant (Y : (Complex A))
    {n m : SimplexCategory} (f : n ⟶ m) :
    let := projectiveModelCategory A K
    weakEquivalences (K ⥤ (Complex A)) ((constantDiagramFrame A K Y).map f) := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  let := projectiveModelCategory A K
  let q := cosimplicialResolutionFamily (carrierProbeFactorization A)
  exact _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.pointwiseTensorFrame_homotopicallyConstant K (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K)
    (q.obj.obj Y) (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight_cofibrant K) (q.cofibrant Y)
    (q.atObject Y).homotopicallyConstant (fibration_app A K) f

/-- 概要：始域 frame の重み付き錐は Kan 複体（Hovey §5.4）。
方針：各複体の fibrancy と始域 frame の Hom の Kan 性を錐へ移す。
規約：元の終域図式にも始域複体にも置換条件を要求しない。
使われ方：定値図式からの実際の導来写像空間の比較。 -/
lemma constantDiagramSourceHom_kanComplex (Y : (Complex A))
    (F : K ⥤ (Complex A)) : SSet.KanComplex ((constantDiagramSourceHom A K Y).obj F) := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  let q := cosimplicialResolutionFamily (carrierProbeFactorization A)
  apply _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.coneSpace_kanComplex K (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K)
    (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight_cofibrant K)
  intro k
  have := complex_isFibrant A (F.obj k)
  exact cosimplicialHom_kanComplex _ (q.cofibrant Y) (q.atObject Y).homotopicallyConstant (F.obj k)

end SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram
