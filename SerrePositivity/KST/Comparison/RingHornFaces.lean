module

public import SerrePositivity.KST.Comparison.RingHornCorrection
public import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits

/-!
# 単体的環のホーンの互換な面と補正誤差

概要：互換な面の値を束ね、既に合わせた面では補正誤差の面が零であることを示す。
方針：単体恒等式とホーンの互換性を環準同型の値で使う。
規約：KST Lemma 2.13 の Kan 性の補助。ここでは次元二以上のホーンを扱う。
使われ方：低い面と高い面からの補正の有限帰納。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Opposite SSet
open scoped Simplicial

/--
概要：次元 n+2 のホーンの互換な面の値。
方針：隣接する順序添字によって面の互換性を表す。
規約：欠けた面 k の値を要求しない。充填の存在はこのデータに含めない。
使われ方：単体的環の加法による実際のホーン充填。
-/
structure RingHornFaces (A : SimplicialObject RingCat.{u}) (n : ℕ) (k : Fin (n + 3)) where
  /--
  概要：欠けた面以外の指定値。
  方針：一つ低い次数の環の元として保持する。
  規約：欠けた面を除く証明を添える。
  使われ方：補正後に一致させる値。
  -/
  face : ∀ (j : Fin (n + 3)), j ≠ k → A.obj (op ⦋n + 1⦌)
  /--
  概要：二つの指定面の共通の面での一致。
  方針：単体恒等式と同じ添字で互換性を表す。
  規約：i≤j に対して i 番目と j+1 番目の面を比較する。
  使われ方：補正誤差の零の面。
  -/
  compatible : ∀ (i j : Fin (n + 2)) (_hij : i ≤ j)
    (hi : i.castSucc ≠ k) (hj : j.succ ≠ k),
    (A.δ j).hom (face i.castSucc hi) = (A.δ i).hom (face j.succ hj)

/--
概要：単体集合の互換なホーンの射を環の元の面のデータへ移す。
方針：Yoneda で各面の元を取り、共通の面での等式を評価する。
規約：Mathlib の horn.IsCompatible をそのまま使う。
使われ方：補正で構成した充填を Kan 性へ戻す。
-/
def RingHornFaces.ofCompatible (A : SimplicialObject RingCat.{u}) {n : ℕ} {k : Fin (n + 3)}
    (f : ∀ (j : Fin (n + 3)), j ≠ k → ((Δ[n + 1] : SSet.{u}) ⟶ ringSpace A))
    (hf : horn.IsCompatible f) : RingHornFaces A n k where
  face j hj := yonedaEquiv (f j hj)
  compatible i j hij hi hj := by
    have hlt : i.castSucc < j.succ := by
      change i.val < j.val + 1
      exact Nat.lt_succ_of_le (Fin.le_iff_val_le_val.mp hij)
    have h := congrArg yonedaEquiv (hf.δ_pred_comp i.castSucc j.succ hi hj hlt)
    simp only [Fin.pred_succ, Fin.castPred_castSucc, stdSimplex.yonedaEquiv_δ_comp] at h
    exact h

/--
概要：低い面を既に合わせていれば、高い面を補正する誤差の対応する面は零である。
方針：二つの面の交換恒等式と指定値の互換性を使う。
規約：i 番目の面を固定し、j+1 番目の面を補正する。
使われ方：低い面を保つ補正の条件。
-/
theorem RingHornFaces.error_face_low (A : SimplicialObject RingCat.{u}) {n : ℕ}
    {k : Fin (n + 3)} (F : RingHornFaces A n k) (y : A.obj (op ⦋n + 2⦌))
    (i j : Fin (n + 2)) (hij : i ≤ j) (hi : i.castSucc ≠ k) (hj : j.succ ≠ k)
    (hy : (A.δ i.castSucc).hom y = F.face i.castSucc hi) :
    (A.δ i).hom (F.face j.succ hj - (A.δ j.succ).hom y) = 0 := by
  rw [map_sub]
  have h : (A.δ i).hom ((A.δ j.succ).hom y) =
      (A.δ j).hom ((A.δ i.castSucc).hom y) :=
    congrArg (fun f => f.hom y) (A.δ_comp_δ hij)
  rw [h, hy, ← F.compatible i j hij hi hj, sub_self]

/--
概要：高い面を既に合わせていれば、低い面を補正する誤差の対応する面は零である。
方針：二つの面の交換恒等式を逆に使い、指定値の互換性と照合する。
規約：j+1 番目の面を固定し、i 番目の面を補正する。
使われ方：高い面を保つ補正の条件。
-/
theorem RingHornFaces.error_face_high (A : SimplicialObject RingCat.{u}) {n : ℕ}
    {k : Fin (n + 3)} (F : RingHornFaces A n k) (y : A.obj (op ⦋n + 2⦌))
    (i j : Fin (n + 2)) (hij : i ≤ j) (hi : i.castSucc ≠ k) (hj : j.succ ≠ k)
    (hy : (A.δ j.succ).hom y = F.face j.succ hj) :
    (A.δ j).hom (F.face i.castSucc hi - (A.δ i.castSucc).hom y) = 0 := by
  rw [map_sub]
  have h : (A.δ i).hom ((A.δ j.succ).hom y) =
      (A.δ j).hom ((A.δ i.castSucc).hom y) :=
    congrArg (fun f => f.hom y) (A.δ_comp_δ hij)
  rw [← h, hy, F.compatible i j hij hi hj, sub_self]

end SerrePositivity.KST.Comparison
