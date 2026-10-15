module

public import SerrePositivity.BhattScholze.DeltaDivisionSourceAlgebras
public import SerrePositivity.HomologicalAlgebra.DerivedBaseChangeDiscrete
public import SerrePositivity.HomologicalAlgebra.TorFlatBaseChangeVanishing
public import SerrePositivity.HomologicalAlgebra.TorSymmetry

/-! # 自由δ射の両因子の係数商に沿うTor消滅

係数射の平坦性と具体的な係数上の式を共通のTor基底変更へ供給する。
係数イデアルの正則性・完備性やG7は要求しない。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
local notation "P₀" => RelativeFreeDeltaRing (R := A) σ

omit [Fact p.Prime] in
/-- 自由δ環での(p,Cd)イデアルは元の係数イデアル(p,d)の拡張。 -/
theorem deltaDivisionSourceCoefficientIdeal_map (d : A) :
    (Ideal.span {(p : A), d}).map (MvPolynomial.C : A →+* P₀) =
      Ideal.span {(p : P₀), MvPolynomial.C d} := by
  rw [Ideal.map_span]
  simp only [Set.image_pair, map_natCast]

/-- 任意の係数商に沿う、実評価βで作用するAの高次Torは零。 -/
theorem deltaDivisionSourceEvaluation_coefficientTorVanishing
    (D : DeltaStructure p A) (a : σ → A) (I : Ideal A) :
    scalarExtensionTorVanishing
      (Ideal.Quotient.mk (I.map (MvPolynomial.C : A →+* P₀)))
      (baseChangeScalarModule (deltaDivisionSourceEval D a)) := by
  let := deltaDivisionSourceEvaluationAlgebra D a
  have hC : (MvPolynomial.C : A →+* P₀).Flat :=
    RingHom.flat_algebraMap_iff.mpr inferInstance
  have hcomp : (algebraMap P₀ A).comp (MvPolynomial.C : A →+* P₀) = RingHom.id A := by
    apply RingHom.ext
    intro r
    exact deltaDivisionSourceEval_C D a r
  have hA : ((algebraMap P₀ A).comp (MvPolynomial.C : A →+* P₀)).Flat := by
    rw [hcomp]
    exact RingHom.Flat.id A
  intro n hn
  cases n with
  | zero => exact (Nat.lt_irrefl 0 hn).elim
  | succ n =>
      let q := Ideal.Quotient.mk (I.map (MvPolynomial.C : A →+* P₀))
      let Mβ := baseChangeScalarModule (deltaDivisionSourceEval D a)
      let Mq := baseChangeScalarModule q
      let : Subsingleton (TorModule P₀ (n + 1) A (P₀ ⧸ I.map MvPolynomial.C)) :=
        torModule_quotient_map_subsingleton (MvPolynomial.C : A →+* P₀) hC A hA I n
      let eT : Mβ ≃ₗ[P₀] A :=
        { toFun := fun z => z
          invFun := fun z => z
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      let eQ : Mq ≃ₗ[P₀] (P₀ ⧸ I.map MvPolynomial.C) :=
        { toFun := fun z => z
          invFun := fun z => z
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl
          map_add' := fun _ _ => rfl
          map_smul' := by
            intro r z
            obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective z
            rfl }
      let e : (((Tor (ModuleCat P₀) (n + 1)).obj Mβ).obj Mq) ≅
          (((Tor (ModuleCat P₀) (n + 1)).obj (ModuleCat.of P₀ A)).obj
            (ModuleCat.of P₀ (P₀ ⧸ I.map MvPolynomial.C))) :=
        ((Tor (ModuleCat P₀) (n + 1)).mapIso eT.toModuleIso).app Mq ≪≫
          ((Tor (ModuleCat P₀) (n + 1)).obj (ModuleCat.of P₀ A)).mapIso eQ.toModuleIso
      let : Subsingleton (TorModule P₀ (n + 1) Mβ Mq) :=
        e.toLinearEquiv.injective.subsingleton
      have hs : Subsingleton (TorModule P₀ (n + 1) Mq Mβ) :=
        (torComm (n + 1) Mq Mβ).injective.subsingleton
      exact ModuleCat.isZero_iff_subsingleton.mpr hs

/-- 任意の係数商に沿う、実自由δ射αで作用する終域の高次Torは零。 -/
theorem deltaDivisionSourceTarget_coefficientTorVanishing
    (D : DeltaStructure p A) (d : A) (I : Ideal A) :
    scalarExtensionTorVanishing
      (Ideal.Quotient.mk (I.map (MvPolynomial.C : A →+* P₀)))
      (baseChangeScalarModule (deltaDivisionSourceMap (σ := σ) D d)) := by
  let := deltaDivisionSourceTargetAlgebra (σ := σ) D d
  let : Module P₀ P₀ := Algebra.toModule
  have hC : (MvPolynomial.C : A →+* P₀).Flat :=
    RingHom.flat_algebraMap_iff.mpr inferInstance
  have hcomp : (algebraMap P₀ P₀).comp (MvPolynomial.C : A →+* P₀) =
      (MvPolynomial.C : A →+* P₀) := by
    apply RingHom.ext
    intro r
    exact deltaDivisionSourceMap_C D d r
  have hP : ((algebraMap P₀ P₀).comp (MvPolynomial.C : A →+* P₀)).Flat := by
    rw [hcomp]
    exact hC
  intro n hn
  cases n with
  | zero => exact (Nat.lt_irrefl 0 hn).elim
  | succ n =>
      let q := Ideal.Quotient.mk (I.map (MvPolynomial.C : A →+* P₀))
      let Mα := baseChangeScalarModule (deltaDivisionSourceMap (σ := σ) D d)
      let Mq := baseChangeScalarModule q
      let : Subsingleton (TorModule P₀ (n + 1) P₀ (P₀ ⧸ I.map MvPolynomial.C)) :=
        torModule_quotient_map_subsingleton (MvPolynomial.C : A →+* P₀) hC P₀ hP I n
      let eT : Mα ≃ₗ[P₀] P₀ :=
        { toFun := fun z => z
          invFun := fun z => z
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      let eQ : Mq ≃ₗ[P₀] (P₀ ⧸ I.map MvPolynomial.C) :=
        { toFun := fun z => z
          invFun := fun z => z
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl
          map_add' := fun _ _ => rfl
          map_smul' := by
            intro r z
            obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective z
            rfl }
      let e : (((Tor (ModuleCat P₀) (n + 1)).obj Mα).obj Mq) ≅
          (((Tor (ModuleCat P₀) (n + 1)).obj (ModuleCat.of P₀ P₀)).obj
            (ModuleCat.of P₀ (P₀ ⧸ I.map MvPolynomial.C))) :=
        ((Tor (ModuleCat P₀) (n + 1)).mapIso eT.toModuleIso).app Mq ≪≫
          ((Tor (ModuleCat P₀) (n + 1)).obj (ModuleCat.of P₀ P₀)).mapIso eQ.toModuleIso
      let : Subsingleton (TorModule P₀ (n + 1) Mα Mq) :=
        e.toLinearEquiv.injective.subsingleton
      have hs : Subsingleton (TorModule P₀ (n + 1) Mq Mα) :=
        (torComm (n + 1) Mq Mα).injective.subsingleton
      exact ModuleCat.isZero_iff_subsingleton.mpr hs

end SerrePositivity.BhattScholze
