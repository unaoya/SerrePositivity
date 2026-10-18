module

public import SerrePositivity.KST.Spectra.FreeUniversalCoverCoordinates

/-!
概要：非斉次関数 cochain の余面写像を標準の群 cochain の式で表す。
方針：任意の単体射の部分積の式を零番目と後続の余面に適用する。
規約：後続の余面は隣接する群元の積を取る contractNth で統一する。
使われ方：Goerss–Jardine VIII §2。Mathlib の非斉次 cochain 微分との比較。
-/

@[expose] public section

universe u

open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra.GroupActionCochains

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：零番目の余面は最初の群元の作用と残りの座標への制限になる。
方針：単体射 δ₀ の部分積を隣接する比で相殺する。
規約：係数は任意の単体集合の作用。
使われ方：Goerss–Jardine VIII §2。群 cochain の微分の第一項。 -/
lemma functionCochains_δ_zero {G : Type u} [Group G] (B : Action SSet.{u} G)
    (n : ℕ) (k : SimplexCategoryᵒᵖ) (x : (Fin n → G) → B.V.obj k)
    (s : Fin (n + 1) → G) :
    ((functionCochains B).map (SimplexCategory.δ (0 : Fin (n + 2)))).app k x s =
      (B.ρ (s 0)).asHom.app k (x (Fin.tail s)) := by
  rw [functionCochains_map_apply]
  change (B.ρ (Fin.partialProd s (0 : Fin (n + 1)).succ)).asHom.app k
      (x (fun i ↦ (Fin.partialProd s i.castSucc.succ)⁻¹ * Fin.partialProd s i.succ.succ)) = _
  have h : (fun i : Fin n ↦ (Fin.partialProd s i.castSucc.succ)⁻¹ *
      Fin.partialProd s i.succ.succ) = Fin.tail s := by
    funext i
    exact Fin.partialProd_right_inv s i.succ
  rw [h, Fin.partialProd_succ]
  simp only [Fin.castSucc_zero, Fin.partialProd_zero, one_mul]

/-- 概要：後続の余面は隣接する群元の積を取る関数の前合成になる。
方針：部分積と succAbove の式を contractNth の比較補題で計算する。
規約：最後の余面では最後の群元を落とす場合も同じ式に含まれる。
使われ方：Goerss–Jardine VIII §2。群 cochain の交代和微分の後続の項。 -/
lemma functionCochains_δ_succ {G : Type u} [Group G] (B : Action SSet.{u} G)
    (n : ℕ) (j : Fin (n + 1)) (k : SimplexCategoryᵒᵖ)
    (x : (Fin n → G) → B.V.obj k) (s : Fin (n + 1) → G) :
    ((functionCochains B).map (SimplexCategory.δ j.succ)).app k x s =
      x (Fin.contractNth j (· * ·) s) := by
  rw [functionCochains_map_apply]
  change (B.ρ (Fin.partialProd s (j.succ.succAbove 0))).asHom.app k
      (x (fun i ↦ (Fin.partialProd s (j.succ.succAbove i.castSucc))⁻¹ *
        Fin.partialProd s (j.succ.succAbove i.succ))) = _
  rw [Fin.succ_succAbove_zero, Fin.partialProd_zero, map_one]
  change x (fun i ↦ (Fin.partialProd s (j.succ.succAbove i.castSucc))⁻¹ *
    Fin.partialProd s (j.succ.succAbove i.succ)) = _
  apply congrArg x
  funext i
  simpa only [Fin.succ_succAbove_succ] using Fin.inv_partialProd_mul_eq_contractNth s j i

end

end SerrePositivity.KST.Spectra.GroupActionCochains
