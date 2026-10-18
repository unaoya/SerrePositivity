module

public import SerrePositivity.KST.Spectra.GroupFunctionCochains

/-!
概要：EG の非斉次座標の構造射と群 cochain の構造射の任意の単体射に対する式。
方針：連続する座標の比の同型と部分積による逆を具体的に評価する。
規約：部分積の零番目は単位元であり、一般の単体射で全ての顔・退化を一括して扱う。
使われ方：Goerss–Jardine VIII §2。cochain の π_* の微分の座標表示への入力。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory SSet

namespace SerrePositivity.KST.Spectra.GroupActionCochains

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：非斉次自由軌道の構造射を部分積と隣接する比で表す。
方針：斉次座標へ戻し、単体射で添字を制限してから再び比を取る。
規約：f の向きは単体的図式の向き。
使われ方：Goerss–Jardine VIII §2。群 cochain の任意の顔・退化の具体的な計算。 -/
lemma freeUniversalCover_map_apply {G : Type u} [Group G]
    {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) (g : G) (s : Fin n.unop.len → G) :
    ((freeUniversalCover G).map f).hom (g, s) =
      (g * Fin.partialProd s (f.unop.toOrderHom 0),
        fun i ↦ (Fin.partialProd s (f.unop.toOrderHom i.castSucc))⁻¹ *
          Fin.partialProd s (f.unop.toOrderHom i.succ)) := by
  change (Action.diagonalSuccIsoTensorTrivial G m.unop.len).hom.hom
      (((Action.diagonalSuccIsoTensorTrivial G n.unop.len).inv.hom (g, s)) ∘
        f.unop.toOrderHom) = _
  erw [Action.diagonalSuccIsoTensorTrivial_inv_hom_apply (G := G) (n := n.unop.len) g s,
    Action.diagonalSuccIsoTensorTrivial_hom_hom_apply (G := G) (n := m.unop.len)]
  apply Prod.ext
  · rfl
  · funext i
    change (g * Fin.partialProd s (f.unop.toOrderHom i.castSucc))⁻¹ *
        (g * Fin.partialProd s (f.unop.toOrderHom i.succ)) = _
    simp only [mul_inv_rev, mul_assoc, inv_mul_cancel_left]

/-- 概要：非斉次関数 cochain の任意の単体射の作用を部分積で表す。
方針：軌道代表 (1,s) の像の座標式を関数の前合成の式へ代入する。
規約：f の向きは余単体 cochain の向き。
使われ方：Goerss–Jardine VIII §2。係数の作用を含む群 cochain の顔・退化の具体式。 -/
lemma functionCochains_map_apply {G : Type u} [Group G] (B : Action SSet.{u} G)
    {n m : SimplexCategory} (f : n ⟶ m) (k : SimplexCategoryᵒᵖ)
    (x : (Fin n.len → G) → B.V.obj k) (s : Fin m.len → G) :
    ((functionCochains B).map f).app k x s =
      (B.ρ (Fin.partialProd s (f.toOrderHom 0))).asHom.app k
        (x (fun i ↦ (Fin.partialProd s (f.toOrderHom i.castSucc))⁻¹ *
          Fin.partialProd s (f.toOrderHom i.succ))) := by
  change (B.ρ (((freeUniversalCover G).map f.op).hom ((1 : G), s)).1).asHom.app k
      (x (((freeUniversalCover G).map f.op).hom ((1 : G), s)).2) = _
  rw [freeUniversalCover_map_apply]
  simp only [one_mul, Quiver.Hom.unop_op]

end

end SerrePositivity.KST.Spectra.GroupActionCochains
