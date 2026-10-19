module

public import SerrePositivity.KST.Spectra.GroupOverCodiscrete
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve

/-!
概要：一対象群圏の nerve の全単体と非斉次群座標の同値。
方針：隣接する射の逆元を座標とし、隣接射から作る composable arrows の普遍性を使う。
規約：SingleObj の合成は逆順の積なので、通常の群 cochain の順序に合わせ逆元を取る。
使われ方：Goerss–Jardine VIII §2。BG の全単体の cochain と非斉次群 cochain の比較。
-/

@[expose] public section

universe u

open CategoryTheory SSet
open scoped Simplicial

namespace SerrePositivity.KST.Spectra.GroupNerve

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (G : Type u) [Group G]

lemma eqToHom_down {a b : AsSmall.{u} (SingleObj G)} (h : a = b) :
    ((eqToHom h).down : G) = 1 := by
  subst b
  rfl

/-- 概要：群の nerve の単体を隣接する射の逆元の列へ送る。
方針：各隣接辺を AsSmall から読み出し逆元を取る。
規約：n 単体は n 個の群の元。
使われ方：Goerss–Jardine VIII §2。標準の非斉次 cochain の座標。 -/
def coordinates {n : ℕ} (s : ComposableArrows (AsSmall.{u} (SingleObj G)) n) : Fin n → G :=
  fun i ↦ ((s.map' i.val (i.val + 1) (by omega) (by omega)).down : G)⁻¹

/-- 概要：非斉次群座標から一対象群圏の nerve の単体を復元する。
方針：全対象を標準対象とし、各隣接射を座標の逆元に指定する。
規約：隣接射からの通常の圏の functor の構成を借りる。
使われ方：Goerss–Jardine VIII §2。BG の関数 cochain の比較の逆写像。 -/
def fromCoordinates {n : ℕ} (a : Fin n → G) :
    ComposableArrows (AsSmall.{u} (SingleObj G)) n :=
  ComposableArrows.mkOfObjOfMapSucc
    (fun _ ↦ GroupOverCodiscrete.star G) (fun i ↦ ULift.up (a i)⁻¹)

lemma coordinates_fromCoordinates {n : ℕ} (a : Fin n → G) :
    coordinates G (fromCoordinates G a) = a := by
  funext i
  dsimp only [coordinates, fromCoordinates]
  rw [ComposableArrows.mkOfObjOfMapSucc_map_succ _ _ i.val i.isLt]
  exact inv_inv _

lemma fromCoordinates_coordinates {n : ℕ}
    (s : ComposableArrows (AsSmall.{u} (SingleObj G)) n) :
    fromCoordinates G (coordinates G s) = s := by
  let h : ∀ i, (fromCoordinates G (coordinates G s)).obj i = s.obj i :=
    fun _ ↦ Subsingleton.elim _ _
  apply ComposableArrows.ext h
  intro i hi
  apply ULift.ext
  dsimp only [fromCoordinates]
  rw [ComposableArrows.mkOfObjOfMapSucc_map_succ _ _ i hi]
  dsimp only [coordinates]
  rw [CategoryTheory.down_comp, CategoryTheory.down_comp]
  change (((s.map' i (i + 1)).down : G)⁻¹)⁻¹ =
    ((eqToHom (h _).symm).down * (s.map' i (i + 1)).down) * (eqToHom (h _)).down
  rw [inv_inv, eqToHom_down, mul_one, one_mul]

/-- 概要：群の nerve の n 単体と n 個の非斉次群座標の同値。
方針：隣接射の逆元と指定隣接射からの復元の往復則を束ねる。
規約：群の有限性は不要。
使われ方：Goerss–Jardine VIII §2。BG の通常の cochain の次数ごとの比較。 -/
def coordinatesEquiv (n : ℕ) : (nerve (AsSmall.{u} (SingleObj G))) _⦋n⦌ ≃ (Fin n → G) where
  toFun := coordinates G
  invFun := fromCoordinates G
  left_inv := fromCoordinates_coordinates G
  right_inv := coordinates_fromCoordinates G

end

end SerrePositivity.KST.Spectra.GroupNerve
