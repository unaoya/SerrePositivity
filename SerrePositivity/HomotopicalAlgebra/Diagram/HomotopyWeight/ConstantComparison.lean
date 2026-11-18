module

public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.PointwiseRealization
public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.PointReplacement
public import Mathlib.CategoryTheory.Limits.Yoneda

/-!
# 一点重みの各値の実現から元の定値図式への比較

概要：Hovey §5.4 の射影一点重みと frame から定値図式への弱同値を構成する。
方針：各値の一点比較を実現し、零次の augmentation へ続ける。
規約：比較は図式の射であり、頂点ごとの逆の選択には依存しない。
使われ方：一般 homotopy 極限の右導来普遍性の始域の置換。
-/

@[expose] public section

noncomputable section

universe u v

namespace SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomotopicalAlgebra
open _root_.SerrePositivity.Reedy _root_.SerrePositivity.HomotopyFunctionComplex

/-- 概要：宇宙を持ち上げた標準零単体は一点と同型（Hovey §5.4）。
方針：Yoneda による終対象の保存と終対象の一意性を使う。
規約：実現の定義と同じ uliftYoneda を使う。
使われ方：一点の frame 実現を零次へ同定する。 -/
def liftedZeroPointIso : uliftYoneda.{u, 0, 0}.obj (SimplexCategory.mk 0) ≅ (⊤_ SSet.{u}) :=
  (SimplexCategory.isTerminalZero.isTerminalObj uliftYoneda.{u, 0, 0} _).uniqueUpToIso
    terminalIsTerminal

variable {C : Type v} [Category.{u} C] [HasColimitsOfSize.{0, u} C]
  (B : SimplexCategory ⥤ C)

/-- 概要：一点の frame 実現は frame の零次と同型（Hovey §5.4）。
方針：実際の Yoneda 拡張の表現可能対象での比較を使う。
規約：frame の零次を別の置換対象へ変えない。
使われ方：定値図式への比較を零次の augmentation へ接続する。 -/
def realizationPointIso : (Realization.functor B).obj (⊤_ SSet.{u}) ≅
    B.obj (SimplexCategory.mk 0) :=
  (Realization.functor B).mapIso _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.liftedZeroPointIso.symm ≪≫
    ((Realization.representableIso B).app (SimplexCategory.mk 0)).symm

variable (K : Type u) [SmallCategory K]

/-- 概要：重みの各値の実現から元の定値図式への自然な比較（Hovey §5.4）。
方針：一点への重み比較を実現し、零次の指定射へ続ける。
規約：元の重みと frame の射だけで構成する。
使われ方：定値図式の cofibrant 置換の弱同値。 -/
def pointwiseFrameComparison {Y : C} (α : B.obj (SimplexCategory.mk 0) ⟶ Y) :
    (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.pointwiseRealization K B).obj (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K) ⟶ (Functor.const K).obj Y :=
  (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.pointwiseRealization K B).map (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.comparison K) ≫
    (Functor.constComp K (⊤_ SSet.{u}) (Realization.functor B)).hom ≫
    (Functor.const K).map ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.realizationPointIso B).hom ≫ α)

variable [ModelCategory C]
  (hB : reedyLeft simplex (cofibrations C) (initial.to B))
  (hconst : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (B.map f))

include hB hconst

/-- 概要：定値図式への比較は各値で弱同値（Hovey §5.4）。
方針：一点重みの境界の右類の実現の弱同値性と零次の同型を使う。
規約：元の零次の比較射の弱同値性を明示する。
使われ方：元の定値図式と cofibrant な実現図式の局所化同型。 -/
lemma pointwiseFrameComparison_weakEquivalence {Y : C}
    (α : B.obj (SimplexCategory.mk 0) ⟶ Y) (hα : weakEquivalences C α) (k : K) :
    weakEquivalences C ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.pointwiseFrameComparison B K α).app k) := by
  have : IsIso (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.realizationPointIso B).hom := (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.realizationPointIso B).isIso_hom
  have he : weakEquivalences C (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.realizationPointIso B).hom :=
    (weakEquivalences C).of_isIso (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.realizationPointIso B).hom
  change weakEquivalences C ((Realization.functor B).map ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.comparison K).app k) ≫
    𝟙 _ ≫ (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.realizationPointIso B).hom ≫ α)
  rw [Category.id_comp]
  exact (weakEquivalences C).comp_mem _ _
    (_root_.SerrePositivity.FrameRealizationLifting.FrameRealizationLifting.map_boundary_rlp_weakEquivalence B hB hconst _ (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.comparison_rlp K k))
    ((weakEquivalences C).comp_mem (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.realizationPointIso B).hom α he hα)

end SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight
