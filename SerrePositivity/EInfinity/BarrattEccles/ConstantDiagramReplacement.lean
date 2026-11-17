module

public import SerrePositivity.EInfinity.BarrattEccles.DiagramModel
public import SerrePositivity.EInfinity.BarrattEccles.MappingFactorizations
public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.ConstantNaturality
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.SimplexResolution

/-!
# 定値 E 代数図式の具体的で関手的な cofibrant 置換

概要：BM 命題 4.1・Hovey §5.4 の生成分解と一点重みで定値図式を置換する。
方針：同じ関手的な始域 frame で重みの各値を実現する。
規約：元の E 代数の cofibrancy を仮定せず、モデル構造は局所的に使う。
使われ方：一般 homotopy 極限の右導来普遍性の定値図式との Hom 比較。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory Limits _root_.HomotopicalAlgebra
open SerrePositivity.Reedy SerrePositivity.HomotopyFunctionComplex

variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]

local instance : HasColimitsOfSize.{0, u} (operad A).Algebra :=
  hasColimitsOfSizeShrink.{0, u} _

/-- 概要：各代数を定値図式の具体的な置換図式へ送る（BM §1、Hovey §5.4）。
方針：関手的な始域 frame の実現を射影一点重みの各値で評価する。
規約：同じ生成分解と重みを全対象・全射に使う。
使われ方：定値図式の局所化後の射の計算。 -/
def constantDiagramReplacement : (operad A).Algebra ⥤ K ⥤ (operad A).Algebra := by
  let := modelCategory A
  exact (cosimplicialResolutionFamily (mappingCofibrantFactorization A)).obj ⋙
    Realization.family ⋙
      (Functor.whiskeringLeft K SSet.{u} (operad A).Algebra).obj (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K)

/-- 概要：置換図式から元の定値図式への実際の自然変換（Hovey §5.4）。
方針：重みの一点比較と始域 frame の零次の augmentation を合成する。
規約：元の代数の射に厳密に自然。
使われ方：定値図式とその cofibrant 置換を局所化で比較する。 -/
def constantDiagramComparison : constantDiagramReplacement A K ⟶ Functor.const K := by
  let := modelCategory A
  let q := cosimplicialResolutionFamily (mappingCofibrantFactorization A)
  refine
    { app := fun Y => _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.pointwiseFrameComparison (q.obj.obj Y) K
        ((q.augmentation.app Y).app (SimplexCategory.mk 0))
      naturality := ?_ }
  intro Y Z f
  apply _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.pointwiseFrameComparison_naturality K (q.obj.map f) f
  exact congr_app (q.augmentation.naturality f) (SimplexCategory.mk 0)

/-- 概要：構成した置換は具体的な射影図式モデルで cofibrant（BM §1、Hovey §5.4）。
方針：重みの射影 cofibrancy と各値の frame 実現の持ち上げを使う。
規約：元の代数の cofibrancy は要求しない。
使われ方：定値図式を始域に持つ図式の導来 Hom の計算。 -/
lemma constantDiagramReplacement_isCofibrant (Y : (operad A).Algebra) :
    let := Diagram.projectiveModelCategory A K
    IsCofibrant ((constantDiagramReplacement A K).obj Y) := by
  let := modelCategory A
  let := Diagram.projectiveModelCategory A K
  let q := cosimplicialResolutionFamily (mappingCofibrantFactorization A)
  apply _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.pointwiseRealization_isCofibrant K (q.obj.obj Y) (q.cofibrant Y)
    _ (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K) (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight_cofibrant K)
  intro F G p hp k
  exact ⟨(Diagram.fibration_iff A K p).mp ⟨hp.1⟩ k,
    (Diagram.weakEquivalence_iff A K p).mp ⟨hp.2⟩ k⟩

/-- 概要：定値図式への比較は各値で元の複体の擬同型（BM §1、Hovey §5.4）。
方針：一点重みの各値の収縮と始域 frame の augmentation を使う。
規約：射は自然変換の同じ成分そのもの。
使われ方：定値図式と置換図式を同じ局所化対象へ同定する。 -/
lemma constantDiagramComparison_quasiIso (Y : (operad A).Algebra) (k : K) :
    QuasiIso (((constantDiagramComparison A K).app Y).app k).hom := by
  let := modelCategory A
  let q := cosimplicialResolutionFamily (mappingCofibrantFactorization A)
  exact _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.pointwiseFrameComparison_weakEquivalence (q.obj.obj Y) K
    (q.cofibrant Y) (q.atObject Y).homotopicallyConstant _
    ((q.atObject Y).augmentation_weakEquivalence (SimplexCategory.mk 0)) k

/-- 概要：定値図式への比較は具体的な図式モデルの弱同値（BM §1、Hovey §5.4）。
方針：各値の擬同型性を図式の弱同値判定に渡す。
規約：図式モデルは局所的に選び、置換の追加仮定は置かない。
使われ方：定値図式と置換図式の普通の局所化での比較。 -/
lemma constantDiagramComparison_weakEquivalence (Y : (operad A).Algebra) :
    let := Diagram.projectiveModelCategory A K
    WeakEquivalence ((constantDiagramComparison A K).app Y) := by
  let := Diagram.projectiveModelCategory A K
  exact (Diagram.weakEquivalence_iff A K _).mpr (constantDiagramComparison_quasiIso A K Y)

/-- 概要：関手的な定値図式置換は代数の擬同型を各値で保つ（Hovey §5.4）。
方針：比較の自然性と二つのうち三つの性質を使う。
規約：元の代数に cofibrancy を要求しない。
使われ方：局所化した定値図式関手と置換関手を比較する。 -/
lemma constantDiagramReplacement_map_quasiIso {Y Z : (operad A).Algebra} (f : Y ⟶ Z)
    (hf : QuasiIso f.hom) (k : K) :
    QuasiIso (((constantDiagramReplacement A K).map f).app k).hom := by
  let := modelCategory A
  have : WeakEquivalence (((constantDiagramComparison A K).app Y).app k) :=
    ⟨constantDiagramComparison_quasiIso A K Y k⟩
  have : WeakEquivalence (((constantDiagramComparison A K).app Z).app k) :=
    ⟨constantDiagramComparison_quasiIso A K Z k⟩
  have : WeakEquivalence f := ⟨hf⟩
  have he : ((constantDiagramReplacement A K).map f).app k ≫
      ((constantDiagramComparison A K).app Z).app k =
    ((constantDiagramComparison A K).app Y).app k ≫ f :=
    congr_app ((constantDiagramComparison A K).naturality f) k
  exact (weakEquivalence_of_postcomp_of_fac he).mem

/-- 概要：置換した定値図式からの射は始域 frame の重み付き錐（Hovey §5.4）。
方針：各値の実現と Hom の実際の随伴を使う。
規約：図式の自然変換と重みの自然変換を全成分で同定する。
使われ方：定値図式を始域とする導来 Hom の重み付き表示。 -/
def constantDiagramHomEquiv (Y : (operad A).Algebra) (F : K ⥤ (operad A).Algebra) :
    let := modelCategory A
    let B := (cosimplicialResolutionFamily (mappingCofibrantFactorization A)).obj.obj Y
    ((constantDiagramReplacement A K).obj Y ⟶ F) ≃
      (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K ⟶ (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.pointwiseFrameHom K B).obj F) := by
  let := modelCategory A
  exact (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.pointwiseRealizationAdjunction K
    ((cosimplicialResolutionFamily (mappingCofibrantFactorization A)).obj.obj Y)).homEquiv _ F

/-- 概要：定値図式と構成した置換は局所化後に自然同型（Hovey §5.4）。
方針：実際の比較自然変換の全成分の弱同値を局所化で反転する。
規約：具体的な図式モデルの普通の局所化を使う。
使われ方：一般 homotopy 極限の導来随伴の左側の定値図式関手。 -/
def constantDiagramLocalizedIso :
    let := Diagram.projectiveModelCategory A K
    let Q := (weakEquivalences (K ⥤ (operad A).Algebra)).Q
    constantDiagramReplacement A K ⋙ Q ≅ (Functor.const K : (operad A).Algebra ⥤ _) ⋙ Q := by
  let := Diagram.projectiveModelCategory A K
  let Q := (weakEquivalences (K ⥤ (operad A).Algebra)).Q
  let c := Functor.whiskerRight (constantDiagramComparison A K) Q
  have : ∀ Y, IsIso (c.app Y) := by
    intro Y
    exact Localization.inverts Q (weakEquivalences (K ⥤ (operad A).Algebra)) _
      (constantDiagramComparison_weakEquivalence A K Y).mem
  have : IsIso c := NatIso.isIso_of_isIso_app c
  exact asIso c

end SerrePositivity.EInfinity.BarrattEccles
