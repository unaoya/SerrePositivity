module

public import SerrePositivity.KST.Comparison.PiZeroRing

/-!
# 単体的環のホーンの退化による補正

概要：一つの退化を加えて隣接する面を補正し、零の面を持つ補正項では他の面を保つ。
方針：単体恒等式を環準同型の値で評価し、加法で補正する。
規約：KST Lemma 2.13 の台加法群の Kan 性を直接証明するための補題。
使われ方：低い面からと高い面からのホーンの有限回の補正。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Opposite
open scoped Simplicial

/--
概要：単体に一つの退化した誤差を加える。
方針：加法と単体的退化を使う。
規約：乗法逆元は使用しない。
使われ方：ホーンの面を一つずつ合わせる。
-/
def ringAddDegeneracy (A : SimplicialObject RingCat.{u}) {n : ℕ}
    (y : A.obj (op ⦋n + 1⦌)) (i : Fin (n + 1)) (e : A.obj (op ⦋n⦌)) :
    A.obj (op ⦋n + 1⦌) := y + (A.σ i).hom e

/--
概要：退化の直前の面では誤差がそのまま加わる。
方針：d_i s_i が恒等である単体恒等式を使う。
規約：任意の単体次数。
使われ方：低い面の補正。
-/
theorem ringAddDegeneracy_face_self (A : SimplicialObject RingCat.{u}) {n : ℕ}
    (y : A.obj (op ⦋n + 1⦌)) (i : Fin (n + 1)) (e : A.obj (op ⦋n⦌)) :
    (A.δ i.castSucc).hom (ringAddDegeneracy A y i e) = (A.δ i.castSucc).hom y + e := by
  unfold ringAddDegeneracy
  rw [map_add]
  have h : (A.δ i.castSucc).hom ((A.σ i).hom e) = e :=
    congrArg (fun f => f.hom e) (A.δ_comp_σ_self (i := i))
  rw [h]

/--
概要：退化の直後の面でも誤差がそのまま加わる。
方針：d_(i+1) s_i が恒等である単体恒等式を使う。
規約：任意の単体次数。
使われ方：高い面の補正。
-/
theorem ringAddDegeneracy_face_succ (A : SimplicialObject RingCat.{u}) {n : ℕ}
    (y : A.obj (op ⦋n + 1⦌)) (i : Fin (n + 1)) (e : A.obj (op ⦋n⦌)) :
    (A.δ i.succ).hom (ringAddDegeneracy A y i e) = (A.δ i.succ).hom y + e := by
  unfold ringAddDegeneracy
  rw [map_add]
  have h : (A.δ i.succ).hom ((A.σ i).hom e) = e :=
    congrArg (fun f => f.hom e) (A.δ_comp_σ_succ (i := i))
  rw [h]

/--
概要：低い面が零である誤差の退化を加えても、対応する低い面は変わらない。
方針：面と退化の交換恒等式で誤差の零の面へ帰着する。
規約：退化の位置より前の面。
使われ方：既に合わせた低い面を保つ。
-/
theorem ringAddDegeneracy_preserves_low (A : SimplicialObject RingCat.{u}) {n : ℕ}
    (y : A.obj (op ⦋n + 2⦌)) (j : Fin (n + 1)) (i : Fin (n + 2))
    (hij : i ≤ j.castSucc) (e : A.obj (op ⦋n + 1⦌)) (he : (A.δ i).hom e = 0) :
    (A.δ i.castSucc).hom (ringAddDegeneracy A y j.succ e) = (A.δ i.castSucc).hom y := by
  unfold ringAddDegeneracy
  rw [map_add]
  have h : (A.δ i.castSucc).hom ((A.σ j.succ).hom e) =
      (A.σ j).hom ((A.δ i).hom e) :=
    congrArg (fun f => f.hom e) (A.δ_comp_σ_of_le hij)
  rw [h, he, map_zero, add_zero]

/--
概要：高い面が零である誤差の退化を加えても、対応する高い面は変わらない。
方針：面と退化を交換し、誤差の零の面を使う。
規約：退化の二つの隣接面より後の面。
使われ方：既に合わせた高い面を保つ。
-/
theorem ringAddDegeneracy_preserves_high (A : SimplicialObject RingCat.{u}) {n : ℕ}
    (y : A.obj (op ⦋n + 2⦌)) (j : Fin (n + 1)) (i : Fin (n + 2))
    (hji : j.castSucc < i) (e : A.obj (op ⦋n + 1⦌)) (he : (A.δ i).hom e = 0) :
    (A.δ i.succ).hom (ringAddDegeneracy A y j.castSucc e) = (A.δ i.succ).hom y := by
  unfold ringAddDegeneracy
  rw [map_add]
  have h : (A.δ i.succ).hom ((A.σ j.castSucc).hom e) =
      (A.σ j).hom ((A.δ i).hom e) :=
    congrArg (fun f => f.hom e) (A.δ_comp_σ_of_gt hji)
  rw [h, he, map_zero, add_zero]

/--
概要：指定した誤差を加えて低い隣接面を任意の値に合わせる。
方針：面の値との差を退化させ、自己減法を打ち消す。
規約：有限回の補正の一段。
使われ方：欠けた面より前の面を順に合わせる。
-/
theorem ringAddDegeneracy_correct_lower (A : SimplicialObject RingCat.{u}) {n : ℕ}
    (y : A.obj (op ⦋n + 1⦌)) (i : Fin (n + 1)) (x : A.obj (op ⦋n⦌)) :
    (A.δ i.castSucc).hom (ringAddDegeneracy A y i (x - (A.δ i.castSucc).hom y)) = x := by
  rw [ringAddDegeneracy_face_self]
  abel

/--
概要：指定した誤差を加えて高い隣接面を任意の値に合わせる。
方針：面の値との差の退化を加える。
規約：有限回の補正の一段。
使われ方：欠けた面より後の面を逆順に合わせる。
-/
theorem ringAddDegeneracy_correct_upper (A : SimplicialObject RingCat.{u}) {n : ℕ}
    (y : A.obj (op ⦋n + 1⦌)) (i : Fin (n + 1)) (x : A.obj (op ⦋n⦌)) :
    (A.δ i.succ).hom (ringAddDegeneracy A y i (x - (A.δ i.succ).hom y)) = x := by
  rw [ringAddDegeneracy_face_succ]
  abel

end SerrePositivity.KST.Comparison
