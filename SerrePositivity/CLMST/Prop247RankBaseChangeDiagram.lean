module

public import SerrePositivity.CLMST.Prop247RankTargets
public import SerrePositivity.CLMST.Prop247RankProduct
public import SerrePositivity.CommutativeAlgebra.TensorProduct.BaseChange

/-! # Prop 2.4.7：原典の rank 像から指定した各対象への実底変換図式

元の R→∏Ri→∏Ti と通常 tensor の標準写像を固定する。
各 Ti は指定した (Ri)_perfd として取ることができる。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.CLMST
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
    (g : R) (hetale : letI := GenericEtale.awayAlgebra R S g
      Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap R S g)))
    (t : Finset ℕ)
abbrev prop247_rankSourceImage (n : ℕ) : Type u :=
  prop247_openSectionImage R (prop247_rankOpen R S g hetale n)
variable (T : t → Type u) [∀ n : t, CommRing (T n)] [∀ n : t, Algebra R (T n)]
    [∀ n : t, Algebra (prop247_rankSourceImage R S g hetale n) (T n)]
    [∀ n : t, IsScalarTower R (prop247_rankSourceImage R S g hetale n) (T n)]

/-- 各元の Ri→Ti を有限直積にした実 R 代数写像。 -/
def prop247_rankTargetProductMap :
    prop247_rankImageProduct R S g hetale t →ₐ[R] (n : t) → T n :=
  AlgHom.pi (fun n => (IsScalarTower.toAlgHom R (prop247_rankSourceImage R S g hetale n) (T n)).comp
    (Pi.evalAlgHom R (fun n : t => prop247_rankSourceImage R S g hetale n) n))

/-- 元の R→∏Ri→∏Ti は、元の R の代数作用そのものである。 -/
theorem prop247_rankTargetProductMap_comp :
    (prop247_rankTargetProductMap R S g hetale t T).comp
      (prop247_toRankImageProduct R S g hetale t) = Algebra.ofId R ((n : t) → T n) := by
  exact Subsingleton.elim _ _

/-- 元の各 Ri→Ti の tensor 比較と、有限直積の標準比較の各座標は可換である。 -/
theorem prop247_rankTargetTensor_square
    (x : (prop247_rankImageProduct R S g hetale t) ⊗[R] S) (n : t) :
    finiteProductBaseChangeEquiv R S T
      (Algebra.TensorProduct.map (prop247_rankTargetProductMap R S g hetale t T)
        (AlgHom.id R S) x) n =
      Algebra.TensorProduct.map
        (IsScalarTower.toAlgHom R (prop247_rankSourceImage R S g hetale n) (T n)) (AlgHom.id R S)
        (finiteProductBaseChangeEquiv R S
          (fun n : t => prop247_rankSourceImage R S g hetale n) x n) :=
  finiteProductBaseChangeEquiv_naturality R S (fun n : t => prop247_rankSourceImage R S g hetale n)
    (fun n => IsScalarTower.toAlgHom R (prop247_rankSourceImage R S g hetale n) (T n)) x n

/-- 元の S から各 Ti⊗R S への標準写像も同じ元を送る。 -/
theorem prop247_rankTargetTensor_unit (s : S) (n : t) :
    finiteProductBaseChangeEquiv R S T
      (Algebra.TensorProduct.map (prop247_rankTargetProductMap R S g hetale t T)
        (AlgHom.id R S) ((1 : prop247_rankImageProduct R S g hetale t) ⊗ₜ[R] s)) n =
      (1 : T n) ⊗ₜ[R] s := by
  rw [Algebra.TensorProduct.map_tmul]
  simp only [map_one, AlgHom.id_apply, finiteProductBaseChangeEquiv_unit]

/-- 指定した各 perfectoid 化に対し、直積係数の有限性と原典の各定 rank の入力を供給する。
Si=Ti⊗R S の有限表示性は元の S の有限表示性から移す。 -/
theorem prop247_rankTargetBaseChange_inputs [Algebra.FinitePresentation R S]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (hf : ∀ n : t, IsPerfectoidization p
      (algebraMap (prop247_rankSourceImage R S g hetale n) (T n))) :
    Module.Finite R ((n : t) → T n) ∧
      ∀ n : t, Module.Finite (T n) (T n ⊗[R] S) ∧
        Algebra.FinitePresentation (T n) (T n ⊗[R] S) ∧
        ∀ x : PrimeSpectrum.basicOpen (algebraMap R (T n) g),
          prop247_awayRank (T n) (T n ⊗[R] S) (algebraMap R (T n) g) x = n.1 := by
  letI := hR.isReduced R p
  letI (n : t) : Module.Finite R (T n) :=
    (prop247_rankTarget_surjective_finite R S p hR g hetale n (T n) (hf n)).2
  refine ⟨inferInstance, ?_⟩
  intro n
  refine ⟨inferInstance, inferInstance, ?_⟩
  intro x
  exact prop247_awayRank_baseChange_over_rankImage R S g hetale n (T n) x

end SerrePositivity.CLMST
