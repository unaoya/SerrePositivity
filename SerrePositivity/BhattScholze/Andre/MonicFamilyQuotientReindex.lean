module

public import SerrePositivity.BhattScholze.Andre.MonicFamilyQuotientUniversal

/-!
# André E1・E2：通常根族商の再添字付け

## 概要

添字集合の同値で多項式族を移しても通常の根族商は元の係数環上で代数同型となる。
BS 著者版 Thm 7.14（p.61）、Rem 7.15（p.62）の有限族から任意族への準備。

## 方針

両方向の指定根への普遍射を作り、係数と根に関する外延性で相互逆性を示す。

## 規約

モニック性や正次数を使わない。宇宙の異なる添字集合の同値も許す。

## 使われ方

有限集合に対する空集合・Option 帰納で根族商の自由性を移す。
-/

@[expose] public noncomputable section

universe u v w

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.BhattScholze.Andre

/-- 概要：同値で再添字付けした多項式族の通常商は元の係数環上で代数同型。
方針：普遍射を両方向に作り、生成元の値から相互逆性を確認する。
規約：多項式族は任意。
使われ方：BS Rem 7.15（著者版 p.62）の有限族の帰納と遷移射の比較。 -/
def polynomialFamilyReindexEquiv {R : Type u} [CommRing R] {σ : Type v} {τ : Type w}
    (e : σ ≃ τ) (f : σ → Polynomial R) :
    PolynomialFamilyQuotient f ≃ₐ[R] PolynomialFamilyQuotient (fun t : τ => f (e.symm t)) := by
  let g := fun t : τ => f (e.symm t)
  let Q := PolynomialFamilyQuotient f
  let T := PolynomialFamilyQuotient g
  let a := fun s : σ => polynomialFamilyQuotientRoot g (e s)
  have ha : ∀ s, (f s).eval₂ (algebraMap R T) (a s) = 0 := by
    intro s
    simpa only [g, Equiv.symm_apply_apply] using polynomialFamilyQuotient_eval g (e s)
  let b := fun t : τ => polynomialFamilyQuotientRoot f (e.symm t)
  have hb : ∀ t, (g t).eval₂ (algebraMap R Q) (b t) = 0 :=
    fun t => polynomialFamilyQuotient_eval f (e.symm t)
  let F := polynomialFamilyQuotientLift f (algebraMap R T) a ha
  let G := polynomialFamilyQuotientLift g (algebraMap R Q) b hb
  have Fcoeff (x : R) : F (algebraMap R Q x) = algebraMap R T x :=
    polynomialFamilyQuotientLift_coeff f _ a ha x
  have Gcoeff (x : R) : G (algebraMap R T x) = algebraMap R Q x :=
    polynomialFamilyQuotientLift_coeff g _ b hb x
  have Froot (s : σ) : F (polynomialFamilyQuotientRoot f s) =
      polynomialFamilyQuotientRoot g (e s) := polynomialFamilyQuotientLift_root f _ a ha s
  have Groot (t : τ) : G (polynomialFamilyQuotientRoot g t) =
      polynomialFamilyQuotientRoot f (e.symm t) := polynomialFamilyQuotientLift_root g _ b hb t
  have hGF : G.comp F = RingHom.id Q := by
    apply polynomialFamilyQuotientHom_ext f
    · intro x
      change G (F (algebraMap R Q x)) = algebraMap R Q x
      rw [Fcoeff, Gcoeff]
    · intro s
      change G (F (polynomialFamilyQuotientRoot f s)) = polynomialFamilyQuotientRoot f s
      rw [Froot, Groot, Equiv.symm_apply_apply]
  have hFG : F.comp G = RingHom.id T := by
    apply polynomialFamilyQuotientHom_ext g
    · intro x
      change F (G (algebraMap R T x)) = algebraMap R T x
      rw [Gcoeff, Fcoeff]
    · intro t
      change F (G (polynomialFamilyQuotientRoot g t)) = polynomialFamilyQuotientRoot g t
      rw [Groot, Froot, Equiv.apply_symm_apply]
  exact
    { toFun := F
      invFun := G
      left_inv := fun x => RingHom.congr_fun hGF x
      right_inv := fun x => RingHom.congr_fun hFG x
      map_mul' := F.map_mul
      map_add' := F.map_add
      commutes' := polynomialFamilyQuotientLift_coeff f _ a ha }

end SerrePositivity.BhattScholze.Andre
