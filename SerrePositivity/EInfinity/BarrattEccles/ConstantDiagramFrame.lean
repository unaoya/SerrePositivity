module

public import SerrePositivity.EInfinity.BarrattEccles.ConstantDiagramReplacement
public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.PointwiseTensorFrame

/-!
# 定値 E 代数図式の具体的な余単体的 frame

概要：BM 命題 4.1・Hovey §5.4 の定値図式置換を全次元の frame へ拡張する。
方針：同じ始域 frame の実現を、標準単体をテンソルした一点重みで評価する。
規約：モデル構造と生成分解は具体的に選び、元の代数の cofibrancy は不要。
使われ方：定値図式からの導来 Hom の重み付き錐表示。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory Limits _root_.HomotopicalAlgebra
open SerrePositivity.Reedy SerrePositivity.HomotopyFunctionComplex
open SerrePositivity.DiagramModel

variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]

local instance : HasColimitsOfSize.{0, u} (operad A).Algebra :=
  hasColimitsOfSizeShrink.{0, u} _

/-- 概要：射影図式の自明 fibration は各値で自明 fibration（BM §1、Hovey §5）。
方針：具体的な図式モデルの二つの右類を評価で判定する。
規約：図式と代数のモデルを局所的に選ぶ。
使われ方：図式の frame の境界持ち上げ。 -/
lemma Diagram.trivialFibration_app :
    let := modelCategory A
    let := Diagram.projectiveModelCategory A K
    ∀ {F G : K ⥤ (operad A).Algebra} (p : F ⟶ G),
      trivialFibrations (K ⥤ (operad A).Algebra) p →
      ∀ k, trivialFibrations (operad A).Algebra (p.app k) := by
  let := modelCategory A
  let := Diagram.projectiveModelCategory A K
  dsimp only
  intro F G p hp k
  exact ⟨(Diagram.fibration_iff A K p).mp ⟨hp.1⟩ k,
    (Diagram.weakEquivalence_iff A K p).mp ⟨hp.2⟩ k⟩

/-- 概要：射影図式の fibration は各値で fibration（BM §1、Hovey §5）。
方針：具体的な右類を各値の全次数全射性で判定する。
規約：全射は元の代数の同じ複体射で判定する。
使われ方：図式の frame のホーン持ち上げ。 -/
lemma Diagram.fibration_app :
    let := modelCategory A
    let := Diagram.projectiveModelCategory A K
    ∀ {F G : K ⥤ (operad A).Algebra} (p : F ⟶ G),
      Fibration p → ∀ k, Fibration (p.app k) := by
  let := modelCategory A
  let := Diagram.projectiveModelCategory A K
  dsimp only
  intro F G p hp k
  exact ⟨(Diagram.fibration_iff A K p).mp hp k⟩

/-- 概要：定値図式の frame を元の代数に関手的に構成する（Hovey §5.4）。
方針：始域 frame 族と各値の実現をテンソルした標準単体で評価する。
規約：全射と合成を保持する実際の関手。
使われ方：定値図式の導来 Hom の二変数の比較。 -/
def constantDiagramFrameFamily :
    (operad A).Algebra ⥤ SimplexCategory ⥤ K ⥤ (operad A).Algebra := by
  let := modelCategory A
  exact (cosimplicialResolutionFamily (mappingCofibrantFactorization A)).obj ⋙
    Realization.family ⋙ Functor.whiskeringRight K SSet.{u} (operad A).Algebra ⋙
      (Functor.whiskeringLeft SimplexCategory (K ⥤ SSet.{u}) (K ⥤ (operad A).Algebra)).obj
        (SSet.stdSimplex ⋙ WeightedCones.tensorDiagram K (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K))

/-- 概要：指定した E 代数の定値図式の実際の frame（Hovey §5.4）。
方針：構成した関手族をその代数で評価する。
規約：全次元で同じ射影重みと始域 frame を使う。
使われ方：図式圏の局所化 Hom の計算。 -/
abbrev constantDiagramFrame (Y : (operad A).Algebra) :
    SimplexCategory ⥤ K ⥤ (operad A).Algebra := (constantDiagramFrameFamily A K).obj Y

/-- 概要：始域 frame の Hom 図式の重み付き錐（Hovey §5.4）。
方針：各値の始域 Hom と錐の実際の右随伴を合成する。
規約：元の代数に cofibrancy を仮定しない。
使われ方：定値図式からの導来 Hom と右 frame の錐の比較。 -/
def constantDiagramSourceHom (Y : (operad A).Algebra) :
    (K ⥤ (operad A).Algebra) ⥤ SSet.{u} := by
  let := modelCategory A
  exact _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.pointwiseWeightedHom K (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K)
    ((cosimplicialResolutionFamily (mappingCofibrantFactorization A)).obj.obj Y)

/-- 概要：図式の frame の Hom は元の始域 frame の錐と同型（Hovey §5.4）。
方針：各値のテンソル実現の随伴と Yoneda 同型を使う。
規約：全単体と終域図式の射に自然。
使われ方：図式の局所化 Hom の重み付き錐表示。 -/
def constantDiagramFrameHomIso (Y : (operad A).Algebra) :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (constantDiagramFrame A K Y) ≅ constantDiagramSourceHom A K Y := by
  let := modelCategory A
  exact _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.pointwiseTensorFrameHomIso K (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K)
    ((cosimplicialResolutionFamily (mappingCofibrantFactorization A)).obj.obj Y)

/-- 概要：図式 frame の零次は構成済みの定値図式置換（Hovey §5.4）。
方針：零単体のテンソル単位同型を各値の実現で送る。
規約：既存の同じ置換図式へ比較する。
使われ方：局所化 Hom の始域の同定。 -/
def constantDiagramFrameZeroIso (Y : (operad A).Algebra) :
    (constantDiagramFrame A K Y).obj (SimplexCategory.mk 0) ≅
      (constantDiagramReplacement A K).obj Y := by
  let := modelCategory A
  exact _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.pointwiseTensorFrameZeroIso K (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K)
    ((cosimplicialResolutionFamily (mappingCofibrantFactorization A)).obj.obj Y)

/-- 概要：定値図式の frame は実際の射影図式モデルで Reedy cofibrant（Hovey §5.4）。
方針：重みの射影 cofibrancy と図式の自明 fibration の評価判定を使う。
規約：元の代数の cofibrancy は不要。
使われ方：図式の導来 Hom の π₀ 比較。 -/
lemma constantDiagramFrame_reedyCofibrant (Y : (operad A).Algebra) :
    let := Diagram.projectiveModelCategory A K
    reedyLeft simplex (cofibrations (K ⥤ (operad A).Algebra))
      (initial.to (constantDiagramFrame A K Y)) := by
  let := modelCategory A
  let := Diagram.projectiveModelCategory A K
  let q := cosimplicialResolutionFamily (mappingCofibrantFactorization A)
  exact _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.pointwiseTensorFrame_reedyCofibrant K (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K)
    (q.obj.obj Y) (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight_cofibrant K) (q.cofibrant Y)
    (Diagram.trivialFibration_app A K)

/-- 概要：定値図式 frame の全単体作用素は図式の弱同値（Hovey §5.4）。
方針：始域 frame の constancy と図式の fibration の評価判定を使う。
規約：図式圏のモデルを局所的に選ぶ。
使われ方：定値図式からの射の連結成分による計算。 -/
lemma constantDiagramFrame_homotopicallyConstant (Y : (operad A).Algebra)
    {n m : SimplexCategory} (f : n ⟶ m) :
    let := Diagram.projectiveModelCategory A K
    weakEquivalences (K ⥤ (operad A).Algebra) ((constantDiagramFrame A K Y).map f) := by
  let := modelCategory A
  let := Diagram.projectiveModelCategory A K
  let q := cosimplicialResolutionFamily (mappingCofibrantFactorization A)
  exact _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.pointwiseTensorFrame_homotopicallyConstant K (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K)
    (q.obj.obj Y) (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight_cofibrant K) (q.cofibrant Y)
    (q.atObject Y).homotopicallyConstant (Diagram.fibration_app A K) f

/-- 概要：始域 frame の重み付き錐は Kan 複体（Hovey §5.4）。
方針：各代数の fibrancy と始域 frame の Hom の Kan 性を錐へ移す。
規約：元の終域図式にも始域代数にも置換条件を要求しない。
使われ方：定値図式からの実際の導来写像空間の比較。 -/
lemma constantDiagramSourceHom_kanComplex (Y : (operad A).Algebra)
    (F : K ⥤ (operad A).Algebra) : SSet.KanComplex ((constantDiagramSourceHom A K Y).obj F) := by
  let := modelCategory A
  let q := cosimplicialResolutionFamily (mappingCofibrantFactorization A)
  apply _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.coneSpace_kanComplex K (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K)
    (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight_cofibrant K)
  intro k
  have := isFibrant A (F.obj k)
  exact cosimplicialHom_kanComplex _ (q.cofibrant Y) (q.atObject Y).homotopicallyConstant (F.obj k)

end SerrePositivity.EInfinity.BarrattEccles
