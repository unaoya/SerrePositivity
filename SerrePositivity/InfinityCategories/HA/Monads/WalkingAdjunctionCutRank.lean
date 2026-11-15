module

public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionFactorCuts

/-!
概要：plusの切れ目とminusの共有点を一つの順位で比較し、同じ単体への輸送と両立させる。
方針：切れ目の座標の2倍に中点の補正を加える。
規約：二つの種類を区別する。使われ方：Riehl–Verity Proposition 3.1.10・Remark 3.3.8、
HA Proposition 4.7.3.3、Kerodon Remark 6.2.1.4（Tag 02EN）の前の分解の一意性。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：中点を区別した水平分解の切れ目の型。
方針：既存の二つの追跡データを場合分けでまとめる。
規約：可換条件を保持する。使われ方：Riehl–Verity Proposition 3.1.10。 -/
def WalkingAdjunctionCut {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (F : Fin (n + 1) ⥤ walkingAdjunctionHom X Y) : WalkingAdjunctionPoint → Type
  | .plus => WalkingAdjunctionPlusCut F
  | .minus => WalkingAdjunctionMinusCut F

/-- 概要：二種類の切れ目の共通の自然数の座標。
方針：元の有限点の値を取る。規約：中点の種類は保持する。
使われ方：Riehl–Verity Proposition 3.1.10 の切れ目の比較。 -/
def walkingAdjunctionCutCoordinate {n : ℕ} {X Y M : WalkingAdjunctionPoint}
    {F : Fin (n + 1) ⥤ walkingAdjunctionHom X Y} (a : WalkingAdjunctionCut F M)
    (i : Fin (n + 1)) : ℕ := by
  cases M
  · exact (a.value i).val
  · exact (a.value i).val

/-- 概要：切れ目と共有点を合わせた順位。
方針：plusは偶数、minusは奇数とする。規約：補正は中点に付ける。
使われ方：Riehl–Verity Proposition 3.1.10 の全分解の比較。 -/
def walkingAdjunctionCutRank {n : ℕ} {X Y M : WalkingAdjunctionPoint}
    {F : Fin (n + 1) ⥤ walkingAdjunctionHom X Y} (a : WalkingAdjunctionCut F M)
    (i : Fin (n + 1)) : ℕ :=
  2 * walkingAdjunctionCutCoordinate a i + walkingAdjunctionTargetCorrection M

variable {n : ℕ} {X Y M N : WalkingAdjunctionPoint}
  {F G : Fin (n + 1) ⥤ walkingAdjunctionHom X Y}

/-- 概要：合成関手の等式に沿って全ての切れ目のデータを移す。
方針：同じ関手に同一視する。規約：新しい切れ目や可換条件を仮定しない。
使われ方：Riehl–Verity Proposition 3.1.10 の同じ実単体の二分解。 -/
def walkingAdjunctionCutTransport (h : F = G) (M : WalkingAdjunctionPoint)
    (a : WalkingAdjunctionCut F M) : WalkingAdjunctionCut G M := h ▸ a

/-- 概要：同じ単体へ移しても各頂点の順位は変わらない。
方針：関手の等式を同一視する。規約：自然数の等式として照合する。
使われ方：Riehl–Verity Proposition 3.1.10 の係数移送。 -/
lemma walkingAdjunctionCutRank_transport (h : F = G) (a : WalkingAdjunctionCut F M)
    (i : Fin (n + 1)) :
    walkingAdjunctionCutRank (walkingAdjunctionCutTransport h M a) i =
      walkingAdjunctionCutRank a i := by
  cases h
  rfl

/-- 概要：任意の二種類の切れ目の順位は全頂点で一貫して比較できる。
方針：同種の場合は各々の全順序、混合の場合はGalois対応の判定を使う。
規約：比較の向きは全頂点で同じ。使われ方：Riehl–Verity Proposition 3.1.10。 -/
lemma walkingAdjunctionCutRank_total (a : WalkingAdjunctionCut F M)
    (b : WalkingAdjunctionCut F N) :
    (∀ i, walkingAdjunctionCutRank a i ≤ walkingAdjunctionCutRank b i) ∨
      (∀ i, walkingAdjunctionCutRank b i ≤ walkingAdjunctionCutRank a i) := by
  cases M <;> cases N
  · rcases WalkingAdjunctionPlusCut.total a b with h | h
    · exact Or.inl (fun i => by
        have hi := h i
        change 2 * (a.value i).val + 0 ≤ 2 * (b.value i).val + 0
        exact Nat.mul_le_mul_left 2 hi)
    · exact Or.inr (fun i => by
        have hi := h i
        change 2 * (b.value i).val + 0 ≤ 2 * (a.value i).val + 0
        exact Nat.mul_le_mul_left 2 hi)
  · rcases walkingAdjunctionCut_mixed_total a b with h | h
    · exact Or.inr (fun i => by
        have hi := h i
        change 2 * (b.value i).val + 1 ≤ 2 * (a.value i).val + 0
        omega)
    · exact Or.inl (fun i => by
        have hi := h i
        change 2 * (a.value i).val + 0 ≤ 2 * (b.value i).val + 1
        omega)
  · rcases walkingAdjunctionCut_mixed_total b a with h | h
    · exact Or.inl (fun i => by
        have hi := h i
        change 2 * (a.value i).val + 1 ≤ 2 * (b.value i).val + 0
        omega)
    · exact Or.inr (fun i => by
        have hi := h i
        change 2 * (b.value i).val + 0 ≤ 2 * (a.value i).val + 1
        omega)
  · rcases WalkingAdjunctionMinusCut.total a b with h | h
    · exact Or.inl (fun i => by
        have hi := h i
        change 2 * (a.value i).val + 1 ≤ 2 * (b.value i).val + 1
        omega)
    · exact Or.inr (fun i => by
        have hi := h i
        change 2 * (b.value i).val + 1 ≤ 2 * (a.value i).val + 1
        omega)

end SerrePositivity.InfinityCategories.HA.Monads
