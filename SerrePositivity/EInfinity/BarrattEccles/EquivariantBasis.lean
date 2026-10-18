module

public import SerrePositivity.EInfinity.BarrattEccles.BasisAction

/-!
# Barratt–Eccles の自由な対称群基底

概要：Berger–Fresse §1.1 の E(n) に基点つき非退化単体と Σₙ の直積で添字づけた基底を与える。
方針：非退化単体による基底を自由軌道分解で添字替えする。
規約：Σₙ は直積の第二成分に右乗法で作用する。
使われ方：Σ-cofibrancy の次数ごとの自由基底となる。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory
open scoped Simplicial

/-- 概要：非退化単体の自由軌道分解の宇宙を持ち上げる（Berger–Fresse §1.1）。
方針：代表の宇宙だけを基礎環の宇宙に合わせる。
規約：群成分は小さい置換群のまま保つ。
使われ方：自由な群基底の添字替えに用いる。 -/
def orbitIndexEquiv (n q : ℕ) :
    ULift.{u} ((simplicial n).nonDegenerate q) ≃
      ULift.{u} (BasedNondegenerate n q) × Equiv.Perm (Fin n) where
  toFun x := (ULift.up (nondegenerateOrbitEquiv n q x.down).1,
    (nondegenerateOrbitEquiv n q x.down).2)
  invFun x := ULift.up ((nondegenerateOrbitEquiv n q).symm (x.1.down, x.2))
  left_inv x := ULift.ext ((nondegenerateOrbitEquiv n q).symm_apply_apply x.down)
  right_inv x := by
    apply Prod.ext
    · apply ULift.ext
      exact congrArg Prod.fst ((nondegenerateOrbitEquiv n q).apply_symm_apply (x.1.down, x.2))
    · change (nondegenerateOrbitEquiv n q
        ((nondegenerateOrbitEquiv n q).symm (x.1.down, x.2))).2 = x.2
      exact congrArg Prod.snd ((nondegenerateOrbitEquiv n q).apply_symm_apply (x.1.down, x.2))

/-- 概要：自由軌道の添字分解は右作用と同変である（Berger–Fresse §1.1）。
方針：非退化単体の自由軌道分解の同変性を成分ごとに持ち上げる。
規約：作用は第二成分にだけ右乗する。
使われ方：添字替えした基底への群作用を計算する。 -/
lemma orbitIndexEquiv_rightAction (n q : ℕ)
    (x : ULift.{u} ((simplicial n).nonDegenerate q)) (σ : Equiv.Perm (Fin n)) :
    orbitIndexEquiv n q (ULift.up (nondegenerateRightAction n q σ x.down)) =
      ((orbitIndexEquiv n q x).1, (orbitIndexEquiv n q x).2 * σ) := by
  have h := nondegenerateOrbitEquiv_rightAction n q x.down σ
  apply Prod.ext
  · exact congrArg (fun y => ULift.up y.1) h
  · change (nondegenerateOrbitEquiv n q (nondegenerateRightAction n q σ x.down)).2 =
      (nondegenerateOrbitEquiv n q x.down).2 * σ
    exact congrArg Prod.snd h

/-- 概要：自由軌道の逆写像も右作用と同変である（Berger–Fresse §1.1）。
方針：添字分解の単射性で順方向の同変性へ帰着する。
規約：代表を固定して群成分に右乗する。
使われ方：基底の添字替え後の右作用の公式となる。 -/
lemma orbitIndexEquiv_symm_rightAction (n q : ℕ)
    (x : ULift.{u} (BasedNondegenerate n q)) (τ σ : Equiv.Perm (Fin n)) :
    ULift.up (nondegenerateRightAction n q σ ((orbitIndexEquiv n q).symm (x, τ)).down) =
      (orbitIndexEquiv n q).symm (x, τ * σ) := by
  apply (orbitIndexEquiv n q).injective
  rw [orbitIndexEquiv_rightAction, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

variable (A : Type u) [CommRing A]

/-- 概要：E(n) の各次数に自由な Σₙ 軌道で添字づけた基底を与える（Berger–Fresse §1.1）。
方針：非退化単体の基底を基点つき代表と置換に分解する。
規約：次数は −q、添字の群成分は右正則作用を受ける。
使われ方：Σₙ 上自由な次数ごとの基底の存在を具体化する。 -/
def equivariantBasis (n q : ℕ) :
    Module.Basis (ULift.{u} (BasedNondegenerate n q) × Equiv.Perm (Fin n)) A
      ((complex A n).X (-(q : ℤ))) :=
  (complexBasis A n q).reindex (orbitIndexEquiv n q)

/-- 概要：自由な群基底への右作用は群成分の右正則作用である（Berger–Fresse §1.1）。
方針：非退化基底の作用の公式を自由軌道の添字替えで移す。
規約：基点つき代表は固定され、τ が τσ に移る。
使われ方：Σ-cofibrancy に必要な次数ごとの自由基底と作用の両立性を示す。 -/
lemma equivariantBasis_rightAction (n q : ℕ)
    (x : ULift.{u} (BasedNondegenerate n q)) (τ σ : Equiv.Perm (Fin n)) :
    (complexRightAction A n σ).f (-(q : ℤ)) (equivariantBasis A n q (x, τ)) =
      equivariantBasis A n q (x, τ * σ) := by
  simp only [equivariantBasis, Module.Basis.reindex_apply,
    complexBasis_rightAction, orbitIndexEquiv_symm_rightAction]

end SerrePositivity.EInfinity.BarrattEccles
