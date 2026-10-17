module

public import SerrePositivity.BhattScholze.Andre.MonicFamilyQuotientUniversal

/-!
# André E1・E2：通常根族商への一変数追加

## 概要

Option で一変数を加えた多項式関係族の商を、先行族の商の上の一元 AdjoinRoot と同定する。
BS 著者版 Thm 7.14（p.61）、Rem 7.15（p.62）の通常モニック根添加の有限族への準備。

## 方針

両方の商の普遍射で相互の環射を作り、係数と標準根上で相互逆性を証明する。
代数同型として元の係数作用も保存する。

## 規約

この同型自体はモニック性や正次数を要求しない。
自由性・忠実平坦性の証明で後からモニック性と正次数を用いる。

## 使われ方

有限族の通常商の自由性と忠実平坦性を一元の結果から帰納する。
-/

@[expose] public noncomputable section

universe u v

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.BhattScholze.Andre

/-- 概要：一変数追加した通常関係商は先行関係商上の一元根添加と代数同型。
方針：指定根への普遍射を両方向に作り、係数と全標準根で相互逆性を検証する。
規約：元の R 係数作用を保ち、モニック性を要求しない。
使われ方：BS Thm 7.14（著者版 p.61）の有限モニック族の通常商の自由性。 -/
def polynomialFamilyOptionEquiv {R : Type u} [CommRing R] {σ : Type v}
    (f : Option σ → Polynomial R) :
    PolynomialFamilyQuotient f ≃ₐ[R]
      AdjoinRoot ((f none).map
        (algebraMap R (PolynomialFamilyQuotient (fun s : σ => f (some s))))) := by
  let f₀ := fun s : σ => f (some s)
  let Q := PolynomialFamilyQuotient f₀
  let g := (f none).map (algebraMap R Q)
  let B := AdjoinRoot g
  let a : Option σ → B := fun s => match s with
    | none => AdjoinRoot.root g
    | some t => algebraMap Q B (polynomialFamilyQuotientRoot f₀ t)
  have ha : ∀ s, (f s).eval₂ (algebraMap R B) (a s) = 0 := by
    intro s
    cases s with
    | none =>
      have h := AdjoinRoot.eval₂_root g
      rw [Polynomial.eval₂_map] at h
      exact h
    | some t =>
      have h := congrArg (algebraMap Q B) (polynomialFamilyQuotient_eval f₀ t)
      rw [Polynomial.hom_eval₂, map_zero] at h
      exact h
  let F := polynomialFamilyQuotientLift f (algebraMap R B) a ha
  have Fcoeff (x : R) : F (algebraMap R (PolynomialFamilyQuotient f) x) =
      algebraMap R B x := polynomialFamilyQuotientLift_coeff f _ a ha x
  have Froot (s : Option σ) : F (polynomialFamilyQuotientRoot f s) = a s :=
    polynomialFamilyQuotientLift_root f _ a ha s
  let b := fun s : σ => polynomialFamilyQuotientRoot f (some s)
  have hb : ∀ s : σ, (f₀ s).eval₂ (algebraMap R (PolynomialFamilyQuotient f)) (b s) = 0 :=
    fun s => polynomialFamilyQuotient_eval f (some s)
  let j := polynomialFamilyQuotientLift f₀ (algebraMap R (PolynomialFamilyQuotient f)) b hb
  have jcoeff (x : R) : j (algebraMap R Q x) =
      algebraMap R (PolynomialFamilyQuotient f) x :=
    polynomialFamilyQuotientLift_coeff f₀ _ b hb x
  have jroot (s : σ) : j (polynomialFamilyQuotientRoot f₀ s) =
      polynomialFamilyQuotientRoot f (some s) :=
    polynomialFamilyQuotientLift_root f₀ _ b hb s
  have hj : j.comp (algebraMap R Q) = algebraMap R (PolynomialFamilyQuotient f) :=
    RingHom.ext jcoeff
  have hg : g.eval₂ j (polynomialFamilyQuotientRoot f none) = 0 := by
    rw [Polynomial.eval₂_map, hj]
    exact polynomialFamilyQuotient_eval f none
  let G := AdjoinRoot.lift j (polynomialFamilyQuotientRoot f none) hg
  have Gcoeff (x : Q) : G (algebraMap Q B x) = j x := AdjoinRoot.lift_of hg
  have Groot : G (AdjoinRoot.root g) = polynomialFamilyQuotientRoot f none :=
    AdjoinRoot.lift_root hg
  have hGF : G.comp F = RingHom.id (PolynomialFamilyQuotient f) := by
    apply polynomialFamilyQuotientHom_ext f
    · intro x
      change G (F (algebraMap R (PolynomialFamilyQuotient f) x)) = _
      rw [Fcoeff]
      change G (algebraMap Q B (algebraMap R Q x)) = _
      rw [Gcoeff, jcoeff]
      rfl
    · intro s
      change G (F (polynomialFamilyQuotientRoot f s)) = _
      rw [Froot]
      cases s with
      | none => exact Groot
      | some t =>
        change G (algebraMap Q B (polynomialFamilyQuotientRoot f₀ t)) = _
        rw [Gcoeff, jroot]
        rfl
  have hFj : F.comp j = algebraMap Q B := by
    apply polynomialFamilyQuotientHom_ext f₀
    · intro x
      change F (j (algebraMap R Q x)) = _
      rw [jcoeff, Fcoeff]
      rfl
    · intro s
      change F (j (polynomialFamilyQuotientRoot f₀ s)) = _
      rw [jroot, Froot]
  have hFG : F.comp G = RingHom.id B := by
    apply AdjoinRoot.ringHom_ext
    · change (F.comp G).comp (AdjoinRoot.of g) = AdjoinRoot.of g
      rw [RingHom.comp_assoc, AdjoinRoot.lift_comp_of]
      exact hFj
    · change F (G (AdjoinRoot.root g)) = AdjoinRoot.root g
      rw [Groot, Froot]
  exact
    { toFun := F
      invFun := G
      left_inv := fun x => RingHom.congr_fun hGF x
      right_inv := fun x => RingHom.congr_fun hFG x
      map_mul' := F.map_mul
      map_add' := F.map_add
      commutes' := Fcoeff }

end SerrePositivity.BhattScholze.Andre
