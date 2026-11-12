module

public import SerrePositivity.KST.Spectra.SphereSimplex

/-!
概要：隣接する二つの面の間の標準 prism 写像。
方針：穴の位置が隣接する二つの単調埋め込みを、区間に沿って切り替える。
規約：始点は i.succ の面、終点は i.castSucc の面。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.2（Tag 00VJ）。RelStruct から実ホモトピーへの変換。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial

namespace SerrePositivity.KST.Spectra.AdjacentFacePrism

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：隣接する穴の埋め込みは頂点ごとに順序を持つ。
方針：succAbove の二つの分岐を比較する。
規約：穴 i+1 の埋め込みは穴 i の埋め込み以下。
使われ方：Kerodon §3.2.2（Tag 00VJ）。prism の単調性。 -/
theorem face_le {n : ℕ} (i j : Fin (n + 1)) :
    i.succ.succAbove j ≤ i.castSucc.succAbove j := by
  unfold Fin.succAbove
  split_ifs <;>
    simp_all only [Fin.le_def, Fin.lt_def, Fin.val_castSucc, Fin.val_succ] <;>
    omega

/-- 概要：隣接する面を区間の値で切り替えた標準単体の単体。
方針：二つの埋め込みの単調性とその間の点ごとの順序を使う。
規約：区間の値が零なら穴 i+1、それ以外なら穴 i。
使われ方：Goerss–Jardine I §7。prism の各単体次数。 -/
def simplex {n d : ℕ} (i : Fin (n + 1)) (s : (Δ[n] : SSet.{u}) _⦋d⦌)
    (t : (Δ[1] : SSet.{u}) _⦋d⦌) : (Δ[n + 1] : SSet.{u}) _⦋d⦌ :=
  stdSimplex.objMk {
    toFun j := if t j = 0 then i.succ.succAbove (s j) else i.castSucc.succAbove (s j)
    monotone' := by
      intro j k hjk
      dsimp only
      have hsjk := stdSimplex.monotone_apply s hjk
      by_cases hj : t j = 0
      · by_cases hk : t k = 0
        · simp only [ite_eq_left hj, ite_eq_left hk]
          exact (Fin.strictMono_succAbove _).monotone hsjk
        · simp only [ite_eq_left hj, ite_eq_right hk]
          exact (face_le i (s j)).trans ((Fin.strictMono_succAbove _).monotone hsjk)
      · by_cases hk : t k = 0
        · have ht := stdSimplex.monotone_apply t hjk
          change t j ≤ t k at ht
          rw [hk] at ht
          exact (hj (le_antisymm ht (Fin.zero_le _))).elim
        · simp only [ite_eq_right hj, ite_eq_right hk]
          exact (Fin.strictMono_succAbove _).monotone hsjk }

/-- 概要：隣接二面の prism 写像。
方針：各次数の切り替えを自然な射へ束ねる。
規約：Δ[n]×Δ[1] から Δ[n+1] への射。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.2（Tag 00VJ）。単一 RelStruct の幾何的表示。 -/
def map {n : ℕ} (i : Fin (n + 1)) : (Δ[n] : SSet.{u}) ⊗ (Δ[1] : SSet.{u}) ⟶
    (Δ[n + 1] : SSet.{u}) where
  app m := ↾(fun p : ((Δ[n] : SSet.{u}).obj m × (Δ[1] : SSet.{u}).obj m) ↦ simplex i p.1 p.2)
  naturality _ _ _ := by
    apply ConcreteCategory.hom_ext
    intro p
    apply stdSimplex.ext
    intro j
    rfl

/-- 概要：prism の始点は一つ後の面。
方針：区間の始点の値を零として評価する。
規約：始点は i.succ。
使われ方：Kerodon §3.2.2（Tag 00VJ）。RelStruct の第二の面のホモトピー端点。 -/
@[reassoc (attr := simp)]
theorem zero {n : ℕ} (i : Fin (n + 1)) : SSet.ι₀ ≫ map.{u} i = stdSimplex.δ i.succ := by
  apply NatTrans.ext
  funext ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  apply stdSimplex.ext
  intro j
  rfl

/-- 概要：prism の終点は一つ前の面。
方針：区間の終点の値を一として評価する。
規約：終点は i.castSucc。
使われ方：Kerodon §3.2.2（Tag 00VJ）。RelStruct の第一の面のホモトピー端点。 -/
@[reassoc (attr := simp)]
theorem one {n : ℕ} (i : Fin (n + 1)) : SSet.ι₁ ≫ map.{u} i = stdSimplex.δ i.castSucc := by
  apply NatTrans.ext
  funext ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  apply stdSimplex.ext
  intro j
  rfl

end

end SerrePositivity.KST.Spectra.AdjacentFacePrism
