module

public import SerrePositivity.EInfinity.BarrattEccles.RightFrames
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Realization

/-!
# 右 frame による実際の E 代数の余テンソル

概要：Hovey §5.4 の右 frame の余テンソルを任意の単体集合で構成する。
方針：反対圏での Yoneda に沿う左 Kan 拡張を反転し、実際の極限を得る。
規約：単体集合のモデル構造は不要、元の E 代数圏に値を取る。
使われ方：一般 homotopy 極限の重み付き end の各成分。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory Opposite
open SerrePositivity.HomotopyFunctionComplex

variable (A : Type u) [CommRing A]

local instance : Limits.HasColimitsOfSize.{0, u} (operad A).Algebraᵒᵖ :=
  Limits.hasColimitsOfSizeShrink.{0, u} _

/-- 概要：右 frame から作る反変な余テンソル（Hovey §5.4）。
方針：反対圏での実際の重み付き実現を反転する。
規約：単体集合の射を E 代数の逆向きの射へ移す。
使われ方：図式の右 frame の重み付き極限。 -/
def cotensor (X : (operad A).Algebra) : SSet.{u}ᵒᵖ ⥤ (operad A).Algebra :=
  (Realization.functor (rightFrame A X)).leftOp

/-- 概要：余テンソルへの射は右 frame の実際の単体的 Hom への射（Hovey §5.4）。
方針：反対圏の Hom の同値と実際の重み付き実現の随伴を合成する。
規約：すべての射は元の E 代数と単体集合の射。
使われ方：余テンソルの普遍性と重み付き錐の比較。 -/
def cotensorHomEquiv (X Y : (operad A).Algebra) (K : SSet.{u}) :
    (Y ⟶ (cotensor A X).obj (op K)) ≃
      (K ⟶ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (rightFrame A X)).obj (op Y)) :=
  (show (Y ⟶ (cotensor A X).obj (op K)) ≃
      ((Realization.functor (rightFrame A X)).obj K ⟶ op Y) from
    { toFun := fun f => f.op
      invFun := fun f => f.unop
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }).trans
    ((Realization.adjunction (rightFrame A X)).homEquiv K (op Y))

/-- 概要：標準単体の余テンソルは右 frame の同じ成分（Hovey §5.4）。
方針：Yoneda に沿う Kan 拡張の表現可能対象での同型を反転する。
規約：任意の宇宙 u に持ち上げた実際の標準単体を使う。
使われ方：境界・ホーンの余テンソルと matching 対象の照合。 -/
def cotensorSimplexIso (X : (operad A).Algebra) (n : SimplexCategory) :
    (cotensor A X).obj (op (uliftYoneda.{u,0,0}.obj n)) ≅
      ((rightFrame A X).obj n).unop :=
  ((Realization.representableIso (rightFrame A X)).app n).unop

end SerrePositivity.EInfinity.BarrattEccles
