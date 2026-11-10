module

public import SerrePositivity.AlgebraicGeometry.AdjoinRootSimpleRootSplit
public import SerrePositivity.AlgebraicGeometry.DeterminantalCenterSplitDescent
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.Unramified.LocalStructure

/-!
概要：標準 étale 代数の中心を、基底環から来る中心の因子にする。
方針：モニック模型にイデアルを引き戻し、底変換後の対角因子から元のイデアルを回収する。
規約：Noether 基底上で、局所中心は境界元の冪を含むものとする。
使われ方：Stacks 0813 の標準 étale チャート上での中心の降下。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open scoped TensorProduct

/--
概要：Noether 基底上の標準 étale 代数の境界冪を含むイデアルは、
基底の境界冪を含む有限生成イデアルを拡張したときの積の因子となる。
方針：モニック模型への縮約と拡張が元のイデアルを回収し、
モニック模型の行列式中心の底変換は対角成分で分解する。
規約：標準 étale 代数は非零とする。
使われ方：étale 局所で得た許容中心を基底側から支配する。
-/
theorem exists_center_factor_standardEtale
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    (P : StandardEtalePair R) [Nontrivial P.Ring]
    (J : Ideal P.Ring) (a : R) (k : ℕ) (ha : algebraMap R P.Ring (a ^ k) ∈ J) :
    ∃ I : Ideal R, I.FG ∧ a ^ (k * (AdjoinRoot.powerBasis' P.monic_f).dim) ∈ I ∧
      ∃ J' : Ideal P.Ring, J'.FG ∧ I.map (algebraMap R P.Ring) = J * J' := by
  let B := P.Ring
  let C := AdjoinRoot P.f
  let h := AdjoinRoot.mk P.f P.g
  let L := Localization.Away h
  let u : B ≃ₐ[R] L := P.equivAwayAdjoinRoot
  let ψ := u.symm.toAlgHom.comp (IsScalarTower.toAlgHom R C L)
  let Jl := J.map u.toRingHom
  let J₀ := Jl.under C
  have hψ : J₀.map ψ.toRingHom = J := by
    change J₀.map (u.symm.toRingHom.comp (algebraMap C L)) = J
    rw [← Ideal.map_map, IsLocalization.map_under (.powers h) L]
    have hu : u.symm.toRingHom.comp u.toRingHom = RingHom.id B :=
      RingHom.ext u.symm_apply_apply
    rw [show Jl = J.map u.toRingHom from rfl, Ideal.map_map, hu, Ideal.map_id]
  have ha₀ : algebraMap R C (a ^ k) ∈ J₀ := by
    change algebraMap C L (algebraMap R C (a ^ k)) ∈ Jl
    rw [← IsScalarTower.algebraMap_apply R C L, ← u.commutes]
    exact Ideal.mem_map_of_mem _ ha
  obtain ⟨g, hg, e, he⟩ := exists_standardEtale_tensor_adjoinRoot_split P
  let D := AdjoinRoot g
  let φ : C →ₐ[R] B := ((AlgHom.fst B B D).comp e.toAlgHom).restrictScalars R |>.comp
    Algebra.TensorProduct.includeRight
  have hφ : φ = ψ := by
    apply AdjoinRoot.algHom_ext
    have hu : u P.X = algebraMap C L (AdjoinRoot.root P.f) := by
      have hx : P.HasMap (algebraMap C L (AdjoinRoot.root P.f)) := by
        constructor
        · rw [Polynomial.aeval_algebraMap_apply, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, map_zero]
        · rw [Polynomial.aeval_algebraMap_apply, AdjoinRoot.aeval_eq]
          exact IsLocalization.Away.algebraMap_isUnit ..
      exact P.lift_X _ hx
    change (e (1 ⊗ₜ[R] AdjoinRoot.root P.f)).1 =
      u.symm (algebraMap C L (AdjoinRoot.root P.f))
    rw [he, ← hu, u.symm_apply_apply]
  obtain ⟨I, hI, hpow, J', heq⟩ := exists_center_factor_of_split_finiteFree
    (AdjoinRoot.powerBasis' P.monic_f).basis (AdjoinRoot.powerBasis' hg).basis e J₀ a k ha₀
  let : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing R B
  refine ⟨I, hI, hpow, J', IsNoetherian.noetherian _, ?_⟩
  change I.map (algebraMap R B) = J₀.map φ.toRingHom * J' at heq
  rwa [hφ, hψ] at heq

/--
概要：Noether 基底上の étale 代数の指定点の主開近傍で、局所中心が
基底側の許容中心の拡張の積の因子となる。
方針：指定点の近くを標準 étale にして、行列式中心の分解を局所化環に戻す。
規約：局所中心は境界元の冪を含むものとする。
使われ方：Stacks 0813 のアフィン形と、0814 の局所中心の貼り合わせ。
-/
theorem exists_center_factor_etale_away
    {R B : Type*} [CommRing R] [IsNoetherianRing R] [CommRing B] [Algebra R B]
    [Algebra.Etale R B] (q : Ideal B) [q.IsPrime]
    (J : Ideal B) (a : R) (k : ℕ) (ha : algebraMap R B (a ^ k) ∈ J) :
    ∃ b : B, b ∉ q ∧ ∃ I : Ideal R, I.FG ∧
      (∃ n : ℕ, a ^ n ∈ I) ∧ ∃ J' : Ideal (Localization.Away b), J'.FG ∧
      I.map (algebraMap R (Localization.Away b)) =
        J.map (algebraMap B (Localization.Away b)) * J' := by
  obtain ⟨b, hb, hbEtale⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := R) q
  let L := Localization.Away b
  let l := IsLocalization.primeSpectrumOrderIso (.powers b) L
  let : Nontrivial L := PrimeSpectrum.nonempty_iff_nontrivial.mp
    ⟨l.symm ⟨⟨q, inferInstance⟩, (Ideal.disjoint_powers_iff_notMem_of_isPrime b).mpr hb⟩⟩
  let p := (Algebra.IsStandardEtale.nonempty_standardEtalePresentation (R := R) (S := L)).some
  let e := p.equivRing
  let : Nontrivial p.P.Ring := e.injective.nontrivial
  let K := J.map (algebraMap B L)
  have hK : algebraMap R L (a ^ k) ∈ K := by
    rw [IsScalarTower.algebraMap_apply R B L]
    exact Ideal.mem_map_of_mem _ ha
  have hke : algebraMap R p.P.Ring (a ^ k) ∈ K.map e.toRingHom := by
    rw [← e.commutes]
    exact Ideal.mem_map_of_mem _ hK
  obtain ⟨I, hI, hpow, I', hI', heq⟩ :=
    exists_center_factor_standardEtale p.P (K.map e.toRingHom) a k hke
  refine ⟨b, hb, I, hI, ⟨_, hpow⟩, I'.map e.symm.toRingHom, hI'.map _, ?_⟩
  have hm := congrArg (Ideal.map e.symm.toRingHom) heq
  have hcomp : e.symm.toRingHom.comp (algebraMap R p.P.Ring) = algebraMap R L :=
    RingHom.ext e.symm.commutes
  have hinv : e.symm.toRingHom.comp e.toRingHom = RingHom.id L :=
    RingHom.ext e.symm_apply_apply
  change (I.map (algebraMap R p.P.Ring)).map e.symm.toRingHom =
    (K.map e.toRingHom * I').map e.symm.toRingHom at hm
  rw [Ideal.map_mul e.symm.toRingHom] at hm
  simpa only [Ideal.map_map, hcomp, hinv, Ideal.map_id] using hm


/--
概要：étale アフィン上の局所中心が基底中心の因子となる主開を有限個で選べる。
方針：局所分解できる主開の元をすべて集め、どの極大イデアルにも同時に入らないことを示す。
規約：局所中心は境界元の冪を含む。
使われ方：Stacks 0814 で、有限個の局所中心を一つの基底中心にまとめる。
-/
theorem exists_finset_away_center_factor_cover
    {R B : Type*} [CommRing R] [IsNoetherianRing R] [CommRing B] [Algebra R B]
    [Algebra.Etale R B] (J : Ideal B) (a : R) (k : ℕ) (ha : algebraMap R B (a ^ k) ∈ J) :
    ∃ s : Finset B, Ideal.span (s : Set B) = ⊤ ∧
      ∀ b ∈ s, ∃ (I : Ideal R) (n : ℕ), a ^ n ∈ I ∧
        ∃ K : Ideal (Localization.Away b), K.FG ∧ I.map (algebraMap R (Localization.Away b)) =
          J.map (algebraMap B (Localization.Away b)) * K := by
  let good : Set B := {b | ∃ (I : Ideal R) (n : ℕ), a ^ n ∈ I ∧
    ∃ K : Ideal (Localization.Away b), K.FG ∧ I.map (algebraMap R (Localization.Away b)) =
      J.map (algebraMap B (Localization.Away b)) * K}
  have hg : Ideal.span good = ⊤ := by
    by_contra h
    obtain ⟨p, hp, hpg⟩ := Ideal.exists_le_maximal (Ideal.span good) h
    obtain ⟨b, hbp, I, _, ⟨n, hn⟩, K, hK, heq⟩ := exists_center_factor_etale_away p J a k ha
    have hb : b ∈ good := ⟨I, n, hn, K, hK, heq⟩
    exact hbp (hpg (Ideal.subset_span hb))
  obtain ⟨s, hs, htop⟩ := (Ideal.span_eq_top_iff_finite good).mp hg
  exact ⟨s, htop, fun b hb => hs hb⟩

end SerrePositivity.AlgebraicGeometry
