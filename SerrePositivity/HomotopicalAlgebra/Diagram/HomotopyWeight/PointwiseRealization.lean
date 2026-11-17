module

public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.Generators
public import SerrePositivity.EInfinity.FrameRealizationLifting
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Finite

/-!
# 重みの各値を固定した frame で実現する関手

概要：Hovey §5.4 の frame の実現を小図式の各値に適用する。
方針：通常の随伴を関手圏へ移し、自由境界の右類を評価で判定する。
規約：単体集合のモデル構造や値圏の局所表示可能性は仮定しない。
使われ方：定値 E 代数図式の具体的な射影 cofibrant 置換。
-/

@[expose] public section

noncomputable section

universe u v

namespace SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomotopicalAlgebra
open _root_.SerrePositivity.Reedy _root_.SerrePositivity.HomotopyFunctionComplex

variable (K : Type u) [SmallCategory K]
  {C : Type v} [Category.{u} C] [HasColimitsOfSize.{0, u} C]
  (B : SimplexCategory ⥤ C)

/-- 概要：重みの各値を同じ frame で実現する関手（Hovey §5.4）。
方針：実際の実現関手を図式に後合成する。
規約：元の添字圏のすべての射を保持する。
使われ方：射影 cofibrant な一点重みから定値図式の置換を構成する。 -/
abbrev pointwiseRealization : (K ⥤ SSet.{u}) ⥤ K ⥤ C :=
  (Functor.whiskeringRight K SSet.{u} C).obj (Realization.functor B)

/-- 概要：frame Hom を図式の各値に適用する関手（Hovey §5.4）。
方針：実際の cosimplicial Hom を図式に後合成する。
規約：frame は添字によらず固定する。
使われ方：射影境界の右類による持ち上げの移送。 -/
abbrev pointwiseFrameHom : (K ⥤ C) ⥤ K ⥤ SSet.{u} :=
  (Functor.whiskeringRight K C SSet.{u}).obj (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom B)

/-- 概要：各値の frame 実現と Hom の実際の随伴（Hovey §5.4）。
方針：元の実現随伴を関手圏へ移す。
規約：モデル構造の存在はこの随伴に不要。
使われ方：重みの射影 cofibration を図式の cofibration へ移す。 -/
def pointwiseRealizationAdjunction :
    _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.pointwiseRealization K B ⊣ _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.pointwiseFrameHom K B := (Realization.adjunction B).whiskerRight K

/-- 概要：各値の frame 実現は実際の左随伴（Hovey §5.4）。
方針：構成済みの関手圏の随伴を使う。
規約：随伴の存在を追加仮定にはしない。
使われ方：初期図式と余極限の保存。 -/
instance pointwiseRealization_isLeftAdjoint : (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.pointwiseRealization K B).IsLeftAdjoint :=
  (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.pointwiseRealizationAdjunction K B).isLeftAdjoint

variable [ModelCategory C] [ModelCategory (K ⥤ C)]
  (hB : reedyLeft simplex (cofibrations C) (initial.to B))
  (htriv : ∀ {F G : K ⥤ C} (p : F ⟶ G), trivialFibrations (K ⥤ C) p →
    ∀ k, trivialFibrations C (p.app k))

include hB htriv

/-- 概要：各値の frame 実現は射影重みの cofibration を保つ（Hovey §5.4）。
方針：各値の自明 fibration の Hom の境界持ち上げを随伴で移す。
規約：図式モデルの右類の各値での判定だけを使う。
使われ方：定値図式の置換の cofibrancy。 -/
lemma pointwiseRealization_map_cofibration {W W' : K ⥤ SSet.{u}} (i : W ⟶ W')
    (hi : (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.boundaries K).rlp.llp i) :
    cofibrations (K ⥤ C) ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.pointwiseRealization K B).map i) := by
  rw [← trivialFibrations_llp]
  intro F G p hp
  apply ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.pointwiseRealizationAdjunction K B).hasLiftingProperty_iff i p).mpr
  apply hi
  apply (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.boundaries_rlp K).ge
  intro k X Y j hj
  obtain ⟨n⟩ := hj
  have : Fibration (p.app k) := ⟨(htriv p hp k).1⟩
  have : WeakEquivalence (p.app k) := ⟨(htriv p hp k).2⟩
  exact boundary_lifting_of_reedyCofibrant B n hB (p.app k)

/-- 概要：射影 cofibrant 重みの各値の実現は cofibrant 図式（Hovey §5.4）。
方針：初期図式からの射の cofibration と左随伴による初期対象の保存を使う。
規約：各値の cofibrancy への置き換えではなく、図式の cofibrancy を得る。
使われ方：定値図式への弱同値を持つ具体的な始域置換。 -/
lemma pointwiseRealization_isCofibrant (W : K ⥤ SSet.{u})
    (hW : (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.boundaries K).rlp.llp (initial.to W)) :
    IsCofibrant ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.pointwiseRealization K B).obj W) := by
  apply (isCofibrant_iff_of_isInitial ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.pointwiseRealization K B).map (initial.to W))
    (initialIsInitial.isInitialObj (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.pointwiseRealization K B) _)).mpr
  exact ⟨_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.pointwiseRealization_map_cofibration K B hB htriv _ hW⟩

end SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight
