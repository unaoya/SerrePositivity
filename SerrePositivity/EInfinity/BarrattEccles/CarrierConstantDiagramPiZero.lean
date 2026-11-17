module

public import SerrePositivity.EInfinity.BarrattEccles.CarrierConstantDiagramFrame
public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.PointwisePiZero

/-!
# 定値 複体図式からの局所化 Hom の重み付き錐表示

概要：BM 命題 4.1・Hovey §5.4 の図式 frame の錐の π₀ で定値図式からの Hom を計算する。
方針：射影図式 frame の π₀ 比較を元の定値図式との弱同値で移す。
規約：元の始域複体と終域図式には cofibrancy・fibrancy の入力仮定を置かない。
使われ方：一般 homotopy 極限の右導来普遍性の定値図式との Hom 比較。
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

attribute [local implicit_reducible] CofibrantResolutionFamily.atObject
  constantDiagramFrameHomIso constantDiagramSourceHom

variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]

local instance : HasColimitsOfSize.{u, u} (Complex A) := ⟨fun _ _ => inferInstance⟩

local instance : HasColimitsOfSize.{0, u} (Complex A) :=
  hasColimitsOfSizeShrink.{0, u} _

/-- 概要：始域 frame の重み付き錐の π₀ は元の定値図式からの Hom（Hovey §5.4）。
方針：図式 frame の零次と置換の局所化同型を通して π₀ 比較を移す。
規約：具体的な射影図式モデルの普通の局所化を使う。
使われ方：一般 homotopy 極限の定値図式との導来随伴の Hom 比較。 -/
def constantDiagramSourcePiZeroEquiv (Y : (Complex A))
    (F : K ⥤ (Complex A)) :
    let := projectiveModelCategory A K
    let Q := (weakEquivalences (K ⥤ (Complex A))).Q
    SSet.π₀ ((constantDiagramSourceHom A K Y).obj F) ≃
      (Q.obj ((Functor.const K).obj Y) ⟶ Q.obj F) := by
  let := SerrePositivity.EInfinity.projectiveModelCategory A
  let := projectiveModelCategory A K
  let q := cosimplicialResolutionFamily (carrierProbeFactorization A)
  let Q := (weakEquivalences (K ⥤ (Complex A))).Q
  have := isFibrant A K F
  exact (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.pointwiseWeightedHomPiZeroEquiv K (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K)
    (q.obj.obj Y) (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight_cofibrant K) (q.cofibrant Y)
    (trivialFibration_app A K) (q.atObject Y).homotopicallyConstant
    (fibration_app A K) Q F).trans
    (Iso.homCongr ((constantDiagramLocalizedIso A K).app Y) (Iso.refl _))

/-- 概要：零単体の錐の像は同じ図式射の局所化（Hovey §5.4）。
方針：図式 frame の零次と定値図式比較の二つの同型を前置する。
規約：元の frame の零単体の射を保持する。
使われ方：図式射の類と導来随伴の単位・余単位の照合。 -/
lemma constantDiagramSourcePiZeroEquiv_mk (Y : (Complex A))
    (F : K ⥤ (Complex A))
    (f : (constantDiagramFrame A K Y).obj (SimplexCategory.mk 0) ⟶ F) :
    let := projectiveModelCategory A K
    let Q := (weakEquivalences (K ⥤ (Complex A))).Q
    constantDiagramSourcePiZeroEquiv A K Y F
      (SSet.mapπ₀ ((constantDiagramFrameHomIso A K Y).app F).hom (SSet.π₀.mk f)) =
      ((constantDiagramLocalizedIso A K).app Y).inv ≫
        Q.map (constantDiagramFrameZeroIso A K Y).inv ≫ Q.map f := by
  let := SerrePositivity.EInfinity.projectiveModelCategory A
  let := projectiveModelCategory A K
  let q := cosimplicialResolutionFamily (carrierProbeFactorization A)
  let Q := (weakEquivalences (K ⥤ (Complex A))).Q
  have := isFibrant A K F
  change ((constantDiagramLocalizedIso A K).app Y).inv ≫
    _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.pointwiseWeightedHomPiZeroEquiv K (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K)
      (q.obj.obj Y) (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight_cofibrant K) (q.cofibrant Y)
      (trivialFibration_app A K) (q.atObject Y).homotopicallyConstant
      (fibration_app A K) Q F _ ≫ 𝟙 _ = _
  have hm : _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.pointwiseWeightedHomPiZeroEquiv K (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K)
      (q.obj.obj Y) (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight_cofibrant K) (q.cofibrant Y)
      (trivialFibration_app A K) (q.atObject Y).homotopicallyConstant
      (fibration_app A K) Q F
      (SSet.mapπ₀ ((constantDiagramFrameHomIso A K Y).app F).hom (SSet.π₀.mk f)) =
    Q.map (constantDiagramFrameZeroIso A K Y).inv ≫ Q.map f :=
    _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.pointwiseWeightedHomPiZeroEquiv_mk K (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K)
      (q.obj.obj Y) (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight_cofibrant K) (q.cofibrant Y)
      (trivialFibration_app A K) (q.atObject Y).homotopicallyConstant
      (fibration_app A K) Q f
  exact (congrArg (fun t : Q.obj ((constantDiagramReplacement A K).obj Y) ⟶ Q.obj F =>
    ((constantDiagramLocalizedIso A K).app Y).inv ≫ t ≫ 𝟙 _) hm).trans
      (by simp only [Category.comp_id]; rfl)

/-- 概要：定値図式からの Hom と錐の π₀ の比較は終域図式の射に自然（Hovey §5.4）。
方針：図式 frame の Hom 同型の自然性と π₀ 比較の自然性を移す。
規約：後合成は同じ元の図式射を局所化したもの。
使われ方：一般 homotopy 極限の Hom 比較を関手的に構成する。 -/
lemma constantDiagramSourcePiZeroEquiv_target (Y : (Complex A))
    {F G : K ⥤ (Complex A)} (g : F ⟶ G)
    (z : SSet.π₀ ((constantDiagramSourceHom A K Y).obj F)) :
    let := projectiveModelCategory A K
    let Q := (weakEquivalences (K ⥤ (Complex A))).Q
    constantDiagramSourcePiZeroEquiv A K Y G
      (SSet.mapπ₀ ((constantDiagramSourceHom A K Y).map g) z) =
      constantDiagramSourcePiZeroEquiv A K Y F z ≫ Q.map g := by
  let := SerrePositivity.EInfinity.projectiveModelCategory A
  let := projectiveModelCategory A K
  let q := cosimplicialResolutionFamily (carrierProbeFactorization A)
  let Q := (weakEquivalences (K ⥤ (Complex A))).Q
  have := isFibrant A K F
  have := isFibrant A K G
  change ((constantDiagramLocalizedIso A K).app Y).inv ≫
      _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.pointwiseWeightedHomPiZeroEquiv K (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K)
        (q.obj.obj Y) (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight_cofibrant K) (q.cofibrant Y)
        (trivialFibration_app A K) (q.atObject Y).homotopicallyConstant
        (fibration_app A K) Q G _ ≫ 𝟙 _ =
    (((constantDiagramLocalizedIso A K).app Y).inv ≫
      _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.pointwiseWeightedHomPiZeroEquiv K (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K)
        (q.obj.obj Y) (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight_cofibrant K) (q.cofibrant Y)
        (trivialFibration_app A K) (q.atObject Y).homotopicallyConstant
        (fibration_app A K) Q F z ≫ 𝟙 _) ≫ Q.map g
  have hn : _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.pointwiseWeightedHomPiZeroEquiv K (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K)
      (q.obj.obj Y) (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight_cofibrant K) (q.cofibrant Y)
      (trivialFibration_app A K) (q.atObject Y).homotopicallyConstant
      (fibration_app A K) Q G (SSet.mapπ₀ ((constantDiagramSourceHom A K Y).map g) z) =
    _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.pointwiseWeightedHomPiZeroEquiv K (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K)
      (q.obj.obj Y) (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight_cofibrant K) (q.cofibrant Y)
      (trivialFibration_app A K) (q.atObject Y).homotopicallyConstant
      (fibration_app A K) Q F z ≫ Q.map g :=
    _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.pointwiseWeightedHomPiZeroEquiv_target K (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K)
      (q.obj.obj Y) (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight_cofibrant K) (q.cofibrant Y)
      (trivialFibration_app A K) (q.atObject Y).homotopicallyConstant
      (fibration_app A K) Q g z
  exact (congrArg (fun t : Q.obj ((constantDiagramReplacement A K).obj Y) ⟶ Q.obj G =>
    ((constantDiagramLocalizedIso A K).app Y).inv ≫ t ≫ 𝟙 _) hn).trans
      (by simp only [Category.comp_id, Category.assoc])

end SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram
