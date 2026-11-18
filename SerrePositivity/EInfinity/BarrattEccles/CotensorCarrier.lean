module

public import SerrePositivity.EInfinity.BarrattEccles.Cotensor
public import Mathlib.CategoryTheory.Adjunction.Opposites
public import Mathlib.CategoryTheory.Functor.KanExtension.Preserves

/-!
# 右 frame の余テンソルの底の複体

概要：BM §1・Hovey §5.4 の余テンソルを忘却後の同じ右 frame で計算する。
方針：極限を保つ忘却関手の反対関手は重み付き実現の左 Kan 拡張を保つ。
規約：複体の frame を再選択せず、代数の frame の底を使う。
使われ方：E2a-4 の一般 homotopy 極限の底の比較。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory Limits Opposite
open SerrePositivity.DifferentialGraded SerrePositivity.HomotopyFunctionComplex

variable (A : Type u) [CommRing A]

/-- 概要：非有界複体は基礎環と同じ宇宙の小極限を持つ（BM §1）。
方針：加群の各形の極限から複体の各形の極限を束ねる。
規約：複体の各次数と微分で計算する既存の極限を使う。
使われ方：忘却後の任意の重み付き end の存在。 -/
instance carrierComplex_hasLimitsOfSize : HasLimitsOfSize.{u, u} (Complex A) where
  has_limits_of_shape _J _ := inferInstance

local instance : HasColimitsOfSize.{0, u} (operad A).Algebraᵒᵖ :=
  hasColimitsOfSizeShrink.{0, u} _
local instance : HasColimitsOfSize.{0, u} (Complex A)ᵒᵖ :=
  hasColimitsOfSizeShrink.{0, u} _

/-- 概要：代数の右 frame の底で計算する複体の余テンソル（BM §1、Hovey §5.4）。
方針：同じ各成分と作用素を忘却し、反対圏で重み付き実現する。
規約：底の複体で新しい置換を選ばない。
使われ方：元の E 代数の余テンソルの底の計算対象。 -/
def carrierCotensor (X : (operad A).Algebra) : SSet.{u}ᵒᵖ ⥤ Complex A :=
  (Realization.functor (rightFrame A X ⋙ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget (operad A)).op)).leftOp

/-- 概要：E 代数の余テンソルの底は同じ frame の複体の余テンソル（BM §1）。
方針：反対忘却の左 Kan 拡張保存の同型を評価して反転する。
規約：任意の単体集合と任意の可換環、モデル構造の入力仮定なし。
使われ方：重み付き homotopy 極限を底の複体で比較する。 -/
def cotensorCarrierIso (X : (operad A).Algebra) (K : SSet.{u}) :
    ((cotensor A X).obj (op K)).carrier ≅ (carrierCotensor A X).obj (op K) := by
  let U := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget (operad A)
  have : U.IsRightAdjoint := (operad A).freeAlgebraAdjunction.isRightAdjoint
  exact ((U.op.leftKanExtensionCompIsoOfPreserves (rightFrame A X)
    uliftYoneda.{u,0,0}).app K).unop.symm

/-- 概要：余テンソルの底の比較は単体集合の射に自然（BM §1、Hovey §5.4）。
方針：左 Kan 拡張の保存同型の逆の自然性を反転する。
規約：余テンソルの反変な向きを保持する。
使われ方：一般 homotopy 極限の重みの制限と忘却の両立。 -/
@[reassoc]
lemma cotensorCarrierIso_naturality (X : (operad A).Algebra)
    {K L : SSet.{u}} (i : K ⟶ L) :
    ((cotensor A X).map i.op).hom ≫ (cotensorCarrierIso A X K).hom =
      (cotensorCarrierIso A X L).hom ≫ (carrierCotensor A X).map i.op := by
  let U := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget (operad A)
  have : U.IsRightAdjoint := (operad A).freeAlgebraAdjunction.isRightAdjoint
  exact (congrArg Quiver.Hom.unop
    ((U.op.leftKanExtensionCompIsoOfPreserves (rightFrame A X)
      uliftYoneda.{u,0,0}).inv.naturality i)).symm

end SerrePositivity.EInfinity.BarrattEccles
