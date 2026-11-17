module
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FramePreservation

public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.TensorRealization
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.PiZero

/-!
# 重み付き錐の連結成分と実現対象からの局所化 Hom

概要：Hovey §5.4 の重み付き錐の π₀ を元の実現対象からの Hom と同定する。
方針：標準 frame の零次を単位のテンソルと同定し、frame の π₀ 比較を移す。
規約：同じ重み・実現対象・局所化を保持し、単体集合モデルは仮定しない。
使われ方：一般 homotopy 極限の擬同型不変性の検出。
-/

@[expose] public section

noncomputable section

universe u v w t

namespace SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
open _root_.HomotopicalAlgebra _root_.SerrePositivity.Reedy _root_.SerrePositivity.HomotopyFunctionComplex
open _root_.SerrePositivity.DiagramModel

variable (K : Type u) [SmallCategory K]

/-- 概要：単位をテンソルした重みは元の重みと同型（Hovey §5.4）。
方針：各値の左単位同型を図式の自然同型に束ねる。
規約：元の重みの図式射を保つ。
使われ方：標準 frame の零次と重み付き実現の比較。 -/
def unitTensorWeightIso (W : K ⥤ SSet.{u}) :
    (WeightedCones.tensorDiagram K W).obj (𝟙_ SSet.{u}) ≅ W :=
  NatIso.ofComponents (fun k => λ_ (W.obj k)) (by
    intro k l f
    exact leftUnitor_naturality (W.map f))

/-- 概要：零単体をテンソルした重みは元の重みと同型（Hovey §5.4）。
方針：零単体の単位同型と左単位同型を合成する。
規約：同じ標準零単体を使う。
使われ方：実現した標準 frame の零次同型。 -/
def zeroTensorWeightIso (W : K ⥤ SSet.{u}) :
    (WeightedCones.tensorDiagram K W).obj (SSet.stdSimplex.obj (SimplexCategory.mk 0)) ≅ W :=
  (WeightedCones.tensorDiagram K W).mapIso QuillenStandardFrame.zeroUnitIso ≪≫
    _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.unitTensorWeightIso K W

variable {C : Type v} [Category.{u} C] [HasColimitsOfSize.{u, u} C] [ModelCategory C]
  (W : Kᵒᵖ ⥤ SSet.{u}) (B : K ⥤ SimplexCategory ⥤ C)

/-- 概要：構成した標準 frame の零次は元の重み付き実現（Hovey §5.4）。
方針：重みの零単体テンソル同型を同じ実現関手で送る。
規約：実現対象を別の置換対象へ変更しない。
使われ方：重み付き錐の π₀ の局所化 Hom 比較。 -/
def tensorFrameZeroIso : (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.tensorFrame K W B).obj (SimplexCategory.mk 0) ≅
    (FrameWeightRealization.functor K B).obj W :=
  (FrameWeightRealization.functor K B).mapIso (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.zeroTensorWeightIso Kᵒᵖ W)

variable (hW : (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.boundaries Kᵒᵖ).rlp.llp (initial.to W))
  (hB : ∀ k, reedyLeft simplex (cofibrations C) (initial.to (B.obj k)))
  (hconst : ∀ k, ∀ {n m : SimplexCategory} (f : n ⟶ m),
    weakEquivalences C ((B.obj k).map f))
  {D : Type w} [Category.{t} D] (L : C ⥤ D) [L.IsLocalization (weakEquivalences C)]

/-- 概要：重み付き錐の連結成分は元の実現対象からの局所化 Hom（Hovey §5.4）。
方針：実際の frame Hom 同型、frame の π₀ 比較、零次同型を合成する。
規約：終域は fibrant、モデル構造は元の値圏だけに置く。
使われ方：係数 frame の弱同値を実現対象の弱同値として検出する。 -/
def frameConePiZeroLocalizationEquiv (Y : C) [IsFibrant Y] :
    SSet.π₀ ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.frameCone K W B).obj Y) ≃
      (L.obj ((FrameWeightRealization.functor K B).obj W) ⟶ L.obj Y) := by
  have hcof := _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.tensorFrame_reedyCofibrant K W B hW hB
  have := cosimplicialFrame_isCofibrant_obj (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.tensorFrame K W B) hcof (SimplexCategory.mk 0)
  exact ((SSet.π₀Functor.mapIso ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.tensorFrameHomIso K W B).app Y).symm).toEquiv).trans
    ((piZeroLocalizationEquiv (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.tensorFrame K W B)
      (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.tensorFrame_homotopicallyConstant K W B hW hB hconst) L hcof Y).trans
      (Iso.homCongr (L.mapIso (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.tensorFrameZeroIso K W B)) (Iso.refl _)))

/-- 概要：零単体の錐の比較は同じ元の射の局所化（Hovey §5.4）。
方針：Hom 同型の逆を相殺し、frame の零次の計算式を使う。
規約：実現対象への零次同型の逆だけを前置する。
使われ方：係数 frame の射に関する π₀ 比較の自然性。 -/
lemma frameConePiZeroLocalizationEquiv_mk {Y : C} [IsFibrant Y]
    (f : (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.tensorFrame K W B).obj (SimplexCategory.mk 0) ⟶ Y) :
    _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.frameConePiZeroLocalizationEquiv K W B hW hB hconst L Y
      (SSet.mapπ₀ ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.tensorFrameHomIso K W B).app Y).hom (SSet.π₀.mk f)) =
      L.map (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.tensorFrameZeroIso K W B).inv ≫ L.map f := by
  have := cosimplicialFrame_isCofibrant_obj (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.tensorFrame K W B)
    (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.tensorFrame_reedyCofibrant K W B hW hB) (SimplexCategory.mk 0)
  change L.map (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.tensorFrameZeroIso K W B).inv ≫
    piZeroLocalizationEquiv (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.tensorFrame K W B)
      (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.tensorFrame_homotopicallyConstant K W B hW hB hconst) L
      (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.tensorFrame_reedyCofibrant K W B hW hB) Y
      (SSet.mapπ₀ ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.tensorFrameHomIso K W B).app Y).inv
        (SSet.mapπ₀ ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.tensorFrameHomIso K W B).app Y).hom (SSet.π₀.mk f))) ≫ 𝟙 _ = _
  rw [← SSet.mapπ₀_comp_apply, Iso.hom_inv_id, SSet.mapπ₀_id_apply,
    piZeroLocalizationEquiv_mk, Category.comp_id]

end SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight
