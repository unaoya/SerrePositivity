module

public import SerrePositivity.InfinityCategories.DoldKanComparison.CubeDifferential

/-!
# 一次立方体の両端と零次評価の閉性

概要：一次立方体の旗の両端を座標面として同定し、全正次元の微分公式を得る。
方針：一点座標の旗を直接計算し、二次元以上の境界公式と合わせる。
規約：一次では微分は1面の評価から0面の評価を引いたもの。
使われ方：HA 1.3.1.16 の辺の閉性と三角形の方程式。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.DoldKanComparison
open CategoryTheory DifferentialGraded DGNerve.PinchedHom
open scoped Simplicial

/-- 概要：一次の最大旗の各端点は対応する座標面の零次旗である。
方針：唯一の座標と唯一の零単体の頂点で所属を計算する。
規約：余面0が1面、余面1が0面。
使われ方：Kerodon 2.5.9 の一次立方体の境界計算。 -/
lemma cubeFlag_one_face {T : Type u} (e : Fin 1 ≃ T) (ε : Bool) :
    (Coherent.cube T).δ (if ε then 0 else 1) (cubeFlag e) =
      (cubeFaceMap e 0 ε).app _
        (cubeFlag (Equiv.ulift.symm : Fin 0 ≃ ULift.{u} (Fin 0))) := by
  refine CategoryTheory.Functor.ext (fun t ↦ ?_)
  have ht : t = (⟨0, by decide⟩ : Fin 1) :=
    Fin.ext (by change t.val = 0; have h : t.val < 1 := t.isLt; omega)
  subst t
  apply Set.ext
  intro a
  obtain ⟨q, rfl⟩ := e.surjective a
  have hq : q = 0 := Subsingleton.elim _ _
  subst q
  change (e.symm (e 0)).val <
    ((if ε then (0 : Fin 2) else 1).succAbove 0).val ↔
      e 0 ∈ cubeFaceOrder e 0 ε _
  rw [e.symm_apply_apply, cubeFaceOrder_mem_fixed]
  cases ε <;> decide

variable {R : Type u} [CommRing R] {D : Type v} [DGCategory R D] {x y : D}

/-- 概要：零次立方体の評価は閉元である。
方針：零次の唯一の旗を評価し、標準零単体の閉性を使う。
規約：微分は Hom の cochain 微分。
使われ方：HA 1.3.1.16 の比較写像の辺が閉射であること。 -/
lemma cubeEvaluation_zero_closed {T : Type u} (e : Fin 0 ≃ T)
    (φ : Coherent.cube T ⟶ standardHomSpace (R := R) x y) :
    differential R (cubeEvaluation e φ) = 0 := by
  rw [cubeEvaluation_zero, cubeFlagEvaluation]
  exact standardTopEval_zero_closed _

/-- 概要：一次立方体の評価の微分は両端の評価の差である。
方針：唯一の旗の微分の二項の和を取り、両端を座標面と同定する。
規約：向きは空集合から全体集合。
使われ方：HA 1.3.1.16 の比較の三角形の方程式の境界側。 -/
lemma cubeEvaluation_one_d {T : Type u} (e : Fin 1 ≃ T)
    (φ : Coherent.cube T ⟶ standardHomSpace (R := R) x y) :
    (homObject R D x y).d (-1) 0 (cubeEvaluation e φ) =
      cubeEvaluation (Equiv.ulift.symm : Fin 0 ≃ ULift.{u} (Fin 0))
        (cubeFaceMap e 0 true ≫ φ) -
      cubeEvaluation (Equiv.ulift.symm : Fin 0 ≃ ULift.{u} (Fin 0))
        (cubeFaceMap e 0 false ≫ φ) := by
  rw [cubeEvaluation_one]
  refine (cubeFlagEvaluation_d (n := 0) e φ).trans ?_
  let F (a : (Coherent.cube T) _⦋0⦌) := standardTopEval (R := R) x y 0 (φ.app _ a)
  refine (Fin.sum_univ_two (fun j : Fin 2 ↦
    (-1 : ℤ) ^ j.val • F ((Coherent.cube T).δ j (cubeFlag e)))).trans ?_
  change (1 : ℤ) • F ((Coherent.cube T).δ 0 (cubeFlag e)) +
    (-1 : ℤ) • F ((Coherent.cube T).δ 1 (cubeFlag e)) = _
  rw [one_smul, neg_one_zsmul]
  rw [show (0 : Fin 2) = (if true then 0 else 1) from rfl, cubeFlag_one_face]
  rw [show (1 : Fin 2) = (if false then 0 else 1) from rfl, cubeFlag_one_face]
  rw [cubeEvaluation_zero, cubeEvaluation_zero]
  exact sub_eq_add_neg _ _ |>.symm

/-- 概要：全ての正次元の立方体評価の微分は座標境界の交代和である。
方針：一次を直接計算し、次元二以上は最大旗の内部面の相殺を使う。
規約：零次元の閉性とは別に、次元 n+1 として述べる。
使われ方：HA 1.3.1.16 の任意の高次成分の微分公式。 -/
lemma cubeEvaluation_succ_d {T : Type u} {n : ℕ} (e : Fin (n + 1) ≃ T)
    (φ : Coherent.cube T ⟶ standardHomSpace (R := R) x y) :
    (homObject R D x y).d (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (cubeEvaluation e φ) =
      ∑ i : Fin (n + 1), (-1 : ℤ) ^ i.val •
        (cubeEvaluation (Equiv.ulift.symm : Fin n ≃ ULift.{u} (Fin n))
          (cubeFaceMap e i true ≫ φ) -
        cubeEvaluation (Equiv.ulift.symm : Fin n ≃ ULift.{u} (Fin n))
          (cubeFaceMap e i false ≫ φ)) := by
  cases n with
  | zero => simpa using cubeEvaluation_one_d e φ
  | succ n => exact cubeEvaluation_d e φ

end SerrePositivity.InfinityCategories.DoldKanComparison
