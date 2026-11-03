module

public import SerrePositivity.CLMST.PerfectoidizationIsogeny.Rank.Targets
public import SerrePositivity.CommutativeAlgebra.RankLocus
public import SerrePositivity.CommutativeAlgebra.TensorProduct.BaseChange
public import SerrePositivity.CommutativeAlgebra.Perfectoid.Defs
public import SerrePositivity.CommutativeAlgebra.ScalarIsogeny
public import SerrePositivity.HomologicalAlgebra.ScalarConeAnnihilators

/-! # 階数の像を通る基底変更の図式と合流

## 概要

元の `R → ∏ R_i → ∏ T_i` と通常のテンソル積の標準写像を固定した基底変更の図式（`rankTargetBaseChange_inputs`）を作り、通常のテンソルの単位・各成分の perfectoid 化・元の普遍性からの比較を合わせて、指定した写像の錐へ合流する（`isogeny_of_actual_rank_comparisons`）。

## 方針

各 `T_i` は指定した `(R_i)_perfd` として取れる。almost 零化は明示的な入力にする。

## 規約

CLMST Prop 2.4.7 の階数ごとの分解の組み立て。旧 `CLMST/Prop247RankBaseChangeDiagram`・`Prop247RankAssembly`。

## 使われ方

`Rank/AIC`・`GeneralRank`。
-/

@[expose] public noncomputable section

universe u

section Prop247RankBaseChangeDiagramPart

namespace SerrePositivity.CLMST
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
    (g : R) (hetale : letI := GenericEtale.awayAlgebra R S g
      Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap R S g)))
    (t : Finset ℕ)
abbrev rankSourceImage (n : ℕ) : Type u :=
  openSectionImage R (rankOpen R S g hetale n)
variable (T : t → Type u) [∀ n : t, CommRing (T n)] [∀ n : t, Algebra R (T n)]
    [∀ n : t, Algebra (rankSourceImage R S g hetale n) (T n)]
    [∀ n : t, IsScalarTower R (rankSourceImage R S g hetale n) (T n)]

/-- 各元の Ri→Ti を有限直積にした実 R 代数写像。 -/
def rankTargetProductMap :
    rankImageProduct R S g hetale t →ₐ[R] (n : t) → T n :=
  AlgHom.pi (fun n => (IsScalarTower.toAlgHom R (rankSourceImage R S g hetale n) (T n)).comp
    (Pi.evalAlgHom R (fun n : t => rankSourceImage R S g hetale n) n))

/-- 元の R→∏Ri→∏Ti は、元の R の代数作用そのものである。 -/
theorem rankTargetProductMap_comp :
    (rankTargetProductMap R S g hetale t T).comp
      (toRankImageProduct R S g hetale t) = Algebra.ofId R ((n : t) → T n) := by
  exact Subsingleton.elim _ _

/-- 元の各 Ri→Ti の tensor 比較と、有限直積の標準比較の各座標は可換である。 -/
theorem rankTargetTensor_square
    (x : (rankImageProduct R S g hetale t) ⊗[R] S) (n : t) :
    finiteProductBaseChangeEquiv R S T
      (Algebra.TensorProduct.map (rankTargetProductMap R S g hetale t T)
        (AlgHom.id R S) x) n =
      Algebra.TensorProduct.map
        (IsScalarTower.toAlgHom R (rankSourceImage R S g hetale n) (T n)) (AlgHom.id R S)
        (finiteProductBaseChangeEquiv R S
          (fun n : t => rankSourceImage R S g hetale n) x n) :=
  finiteProductBaseChangeEquiv_naturality R S (fun n : t => rankSourceImage R S g hetale n)
    (fun n => IsScalarTower.toAlgHom R (rankSourceImage R S g hetale n) (T n)) x n

/-- 元の S から各 Ti⊗R S への標準写像も同じ元を送る。 -/
theorem rankTargetTensor_unit (s : S) (n : t) :
    finiteProductBaseChangeEquiv R S T
      (Algebra.TensorProduct.map (rankTargetProductMap R S g hetale t T)
        (AlgHom.id R S) ((1 : rankImageProduct R S g hetale t) ⊗ₜ[R] s)) n =
      (1 : T n) ⊗ₜ[R] s := by
  rw [Algebra.TensorProduct.map_tmul]
  simp only [map_one, AlgHom.id_apply, finiteProductBaseChangeEquiv_unit]

/-- 指定した各 perfectoid 化に対し、直積係数の有限性と原典の各定 rank の入力を供給する。
Si=Ti⊗R S の有限表示性は元の S の有限表示性から移す。 -/
theorem rankTargetBaseChange_inputs [Algebra.FinitePresentation R S]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (hf : ∀ n : t, IsPerfectoidization p
      (algebraMap (rankSourceImage R S g hetale n) (T n))) :
    Module.Finite R ((n : t) → T n) ∧
      ∀ n : t, Module.Finite (T n) (T n ⊗[R] S) ∧
        Algebra.FinitePresentation (T n) (T n ⊗[R] S) ∧
        ∀ x : PrimeSpectrum.basicOpen (algebraMap R (T n) g),
          awayRank (T n) (T n ⊗[R] S) (algebraMap R (T n) g) x = n.1 := by
  letI := hR.isReduced R p
  letI (n : t) : Module.Finite R (T n) :=
    (rankTarget_surjective_finite R S p hR g hetale n (T n) (hf n)).2
  refine ⟨inferInstance, ?_⟩
  intro n
  refine ⟨inferInstance, inferInstance, ?_⟩
  intro x
  exact awayRank_baseChange_over_rankImage R S g hetale n (T n) x

end SerrePositivity.CLMST

end Prop247RankBaseChangeDiagramPart

section Prop247RankAssemblyPart

namespace SerrePositivity.CLMST
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    {ι : Type*} [Finite ι] (T : ι → Type u)
    [∀ i, CommRing (T i)] [∀ i, Algebra R (T i)]

/-- 元の S を各元の Ti⊗R S に送る標準代数写像の直積。 -/
def rankTensorUnit : S →ₐ[R] (i : ι) → T i ⊗[R] S :=
  AlgHom.pi (fun _ => Algebra.TensorProduct.includeRight)

/-- 元の R→∏Ti の almost 条件から、元の S→∏(Ti⊗R S) の核・余核を g² で消す。
S の平坦性は要求しない。 -/
theorem rankTensorUnit_ker_coker (g : R)
    (hk : ∀ x : (Algebra.linearMap R ((i : ι) → T i)).ker, g • x = 0)
    (hc : ∀ y : ((i : ι) → T i) ⧸ (Algebra.linearMap R ((i : ι) → T i)).range,
      g • y = 0) :
    (∀ x : (rankTensorUnit R S T).toLinearMap.ker, g ^ 2 • x = 0) ∧
      (∀ y : ((i : ι) → T i ⊗[R] S) ⧸ (rankTensorUnit R S T).toLinearMap.range,
        g ^ 2 • y = 0) := by
  let u := TensorProduct.mk R ((i : ι) → T i) S (1 : (i : ι) → T i)
  let s := (rankTensorUnit R S T).toLinearMap
  let e := (finiteProductBaseChangeEquiv R S T).toLinearEquiv.restrictScalars R
  have he (x : S) : e (u x) = s x := by
    ext i
    exact finiteProductBaseChangeEquiv_unit R S T x i
  obtain ⟨hk0, hc0⟩ := tensor_unit_ker_coker_annihilated R ((i : ι) → T i) S g g hk hc
  constructor
  · intro x
    apply Subtype.ext
    change g ^ 2 • (x : S) = 0
    have hx0 : u (x : S) = 0 := e.injective (by rw [he, map_zero]; exact x.property)
    have h := congrArg Subtype.val (hk0 ⟨(x : S), hx0⟩)
    change (g * g) • (x : S) = 0 at h
    simpa only [pow_two] using h
  · intro y
    obtain ⟨y, rfl⟩ := s.range.mkQ_surjective y
    have hm : (g * g) • e.symm y ∈ u.range := by
      apply (Submodule.Quotient.mk_eq_zero u.range).mp
      exact (u.range.mkQ.map_smul (g * g) (e.symm y)).trans (hc0 _)
    obtain ⟨x, hx⟩ := hm
    rw [← map_smul]
    apply (Submodule.Quotient.mk_eq_zero s.range).mpr
    refine ⟨x, ?_⟩
    calc
      s x = e (u x) := (he x).symm
      _ = e ((g * g) • e.symm y) := congrArg e hx
      _ = g ^ 2 • y := by rw [map_smul, e.apply_symm_apply, pow_two]

variable (p : ℕ) [Fact p.Prime] (C : Type u) [CommRing C] [Algebra R C]
    (f : S →ₐ[R] C) (hf : IsPerfectoidization p f.toRingHom)
    (P : ι → Type u) [∀ i, CommRing (P i)] [∀ i, Algebra R (P i)]
    (β : ∀ i, T i ⊗[R] S →ₐ[R] P i)
    (hβ : ∀ i, IsPerfectoidization p (β i).toRingHom)

/-- 元の指定 perfectoid 化から各指定 perfectoid 化への元の誘導写像の直積。 -/
def rankPerfectoidComparison : C →ₐ[R] (i : ι) → P i :=
  AlgHom.pi (fun i => IsPerfectoidization.mapAlgHom hf (hβ i)
    (Algebra.TensorProduct.includeRight : S →ₐ[R] T i ⊗[R] S))

/-- 元の単位と元の誘導写像が、元の各 βi と実可換図式をなす。 -/
theorem rankPerfectoidComparison_square :
    (rankPerfectoidComparison R S T p C f hf P β hβ).toLinearMap.comp f.toLinearMap =
      (LinearMap.piMap (fun i => (β i).toLinearMap)).comp
        (rankTensorUnit R S T).toLinearMap := by
  ext x i
  exact AlgHom.congr_fun (IsPerfectoidization.mapAlgHom_comp hf (hβ i)
    (Algebra.TensorProduct.includeRight : S →ₐ[R] T i ⊗[R] S)) x

/-- rank 比較の実データと有限成分の錐零化を元の f の実錐へ合流する。
almost 条件は係数写像の核・余核と元の perfectoid 比較の核だけを明示する。 -/
theorem isogeny_of_actual_rank_comparisons (g : R) (a b : ℕ)
    (hk : ∀ x : (Algebra.linearMap R ((i : ι) → T i)).ker, g ^ a • x = 0)
    (hc : ∀ y : ((i : ι) → T i) ⧸ (Algebra.linearMap R ((i : ι) → T i)).range,
      g ^ a • y = 0)
    (htk : ∀ x : (rankPerfectoidComparison R S T p C f hf P β hβ).toLinearMap.ker,
      g ^ b • x = 0)
    (hcomponent : ∀ i, ∃ q : ℕ,
      (∀ x : (β i).toLinearMap.ker, g ^ q • x = 0) ∧
        (∀ y : P i ⧸ (β i).toLinearMap.range, g ^ q • y = 0)) :
    ∃ q : ℕ, moduleMapConeScalar R f.toLinearMap (g ^ q) = 0 := by
  obtain ⟨hsk, hsc⟩ := rankTensorUnit_ker_coker R S T (g ^ a) hk hc
  obtain ⟨q, hhk, hhc⟩ := exists_uniform_pow_ker_coker_piMap
    (fun i => (β i).toLinearMap) g hcomponent
  have hcone := moduleMapConeScalar_of_comparison_square f.toLinearMap
    (rankTensorUnit R S T).toLinearMap
    (LinearMap.piMap (fun i => (β i).toLinearMap))
    (rankPerfectoidComparison R S T p C f hf P β hβ).toLinearMap
    (rankPerfectoidComparison_square R S T p C f hf P β hβ)
    (g ^ (a * 2)) (g ^ (a * 2)) (g ^ q) (g ^ q) (g ^ b)
    (by simpa only [pow_mul] using hsk) (by simpa only [pow_mul] using hsc) hhk hhc htk
  exact ⟨(a * 2 + q) + (b + a * 2 + q), by simpa only [← pow_add] using hcone⟩

end SerrePositivity.CLMST

end Prop247RankAssemblyPart
