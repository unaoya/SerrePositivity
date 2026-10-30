module

public import SerrePositivity.CommutativeAlgebra.MinimalGenerators
public import SerrePositivity.HomologicalAlgebra.TorLES
public import Mathlib.Algebra.Homology.Embedding.StupidTrunc
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import SerrePositivity.HomologicalAlgebra.Complex.Truncation

/-! # Noether 局所環上の極小自由分解

## 概要

剰余体の基底から作った極小自由被覆を各核に繰り返し適用して、Noether 局所環上の有限生成加群の極小自由分解を作る。その階数は Betti 数 `ℓ(Tor_i(M, k))` に等しく（`length_tor`）、`0,…,l` 次の有限切り詰めは有限自由な項と微分の極小性を保つ。加群の消去元は分解で零ホモトピックになり、切り詰めた後の作用は直前の Betti 数を階数とする一項複体を経由する。

## 方針

階数と Betti 数は、第 1 変数の Tor の長完全列で極小被覆の核に沿って次数をずらして比べる。Tor の一般の対称性は使わない。Noether 性は核の有限生成性だけに使う。

## 規約

環の正則性や分解の有界性は仮定しない。`TruncationBoundary.boundary` と同名の `boundary` は特殊化の関係にある（refactor-plan §3.2.3）。

## 使われ方

Asymptotic の極小分解の族と Betti 数の評価、Paper の §5。
-/

@[expose] public noncomputable section

universe u

section MinimalFreeResolutionPart

open CategoryTheory Limits

namespace SerrePositivity.MinimalFreeResolution

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable (M : FGModuleCat.{u} R)

/-- 極小被覆の核を繰り返して得る有限生成の syzygy。 -/
noncomputable def syzygy : ℕ → FGModuleCat.{u} R
  | 0 => M
  | n + 1 => FGModuleCat.of R (LinearMap.ker (MinimalGenerators.π (syzygy n)))

/-- 極小分解の各項。 -/
noncomputable abbrev term (n : ℕ) : ModuleCat.{u} R :=
  MinimalGenerators.cover (syzygy M n)

/-- 各項から syzygy への全射。 -/
noncomputable abbrev π (n : ℕ) : term M n →ₗ[R] syzygy M n :=
  MinimalGenerators.π (syzygy M n)

/-- syzygy を前の自由項の核として埋め込む。 -/
noncomputable def ι (n : ℕ) : syzygy M (n + 1) →ₗ[R] term M n :=
  (LinearMap.ker (π M n)).subtype

lemma ι_injective (n : ℕ) : Function.Injective (ι M n) := Subtype.val_injective

lemma π_surjective (n : ℕ) : Function.Surjective (π M n) :=
  MinimalGenerators.π_surjective _

lemma exact_ι_π (n : ℕ) : Function.Exact (ι M n) (π M n) :=
  LinearMap.exact_subtype_ker_map _

/-- 極小自由分解の隣接する項の微分。 -/
noncomputable def d (n : ℕ) : term M (n + 1) ⟶ term M n :=
  ModuleCat.ofHom ((ι M n).comp (π M (n + 1)))

lemma d_comp_d (n : ℕ) : d M (n + 1) ≫ d M n = 0 := by
  ext x
  change ι M n (π M (n + 1) (ι M (n + 1) (π M (n + 2) x))) = 0
  rw [(exact_ι_π M (n + 1)).apply_apply_eq_zero, map_zero]

/-- 自然数添字の極小自由複体。 -/
noncomputable def complex : ChainComplex (ModuleCat.{u} R) ℕ :=
  ChainComplex.of (term M) (d M) (d_comp_d M)

@[simp] lemma complex_d (n : ℕ) : (complex M).d (n + 1) n = d M n :=
  ChainComplex.of_d _ _ n

lemma exact_d_π : Function.Exact (d M 0).hom (π M 0) := by
  rw [LinearMap.exact_iff]
  change LinearMap.ker (π M 0) = LinearMap.range ((ι M 0).comp (π M 1))
  rw [LinearMap.range_comp_of_range_eq_top _
    (LinearMap.range_eq_top.mpr (π_surjective M 1))]
  exact (LinearMap.exact_iff.mp (exact_ι_π M 0))

lemma exact_d_d (n : ℕ) : Function.Exact (d M (n + 1)).hom (d M n).hom := by
  rw [LinearMap.exact_iff]
  change LinearMap.ker ((ι M n).comp (π M (n + 1))) =
    LinearMap.range ((ι M (n + 1)).comp (π M (n + 2)))
  rw [LinearMap.ker_comp, LinearMap.ker_eq_bot.mpr (ι_injective M n), Submodule.comap_bot,
    LinearMap.range_comp_of_range_eq_top _
      (LinearMap.range_eq_top.mpr (π_surjective M (n + 2)))]
  exact LinearMap.exact_iff.mp (exact_ι_π M (n + 1))

/-- 増大射と完全性を備えた極小射影分解。全ての項は有限自由である。 -/
noncomputable def resolution : ProjectiveResolution M.obj := by
  let g : (complex M).X 0 ⟶ M.obj := ModuleCat.ofHom (π M 0)
  have hg : (complex M).d 1 0 ≫ g = 0 := by
    ext x
    exact (exact_d_π M).apply_apply_eq_zero x
  refine { complex := complex M, projective := ?_, π :=
    (ChainComplex.toSingle₀Equiv (complex M) M.obj).symm ⟨g, hg⟩, quasiIso := ?_ }
  · intro n
    change Projective (term M n)
    infer_instance
  · constructor
    intro n
    cases n with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
      · exact ⟨(ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr (exact_d_π M),
          (ModuleCat.epi_iff_surjective g).mpr (π_surjective M 0)⟩
      all_goals rfl
    | succ n =>
      rw [quasiIsoAt_iff_exactAt' _ _ (ChainComplex.exactAt_succ_single_obj _ _)]
      rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp)]
      apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
      change Function.Exact ((complex M).d (n + 2) (n + 1)).hom
        ((complex M).d (n + 1) n).hom
      simp only [complex_d]
      exact exact_d_d M n

@[simp] lemma resolution_complex : (resolution M).complex = complex M := rfl

/-- 極小分解を整数添字に延長しても、各項は自由である。 -/
instance extRes_free (q : ℤ) : Module.Free R ((extRes (resolution M)).X q) := by
  by_cases hq : 0 < q
  · have := ModuleCat.subsingleton_of_isZero (extRes_isZero_X (resolution M) q hq)
    exact Module.Free.of_subsingleton _ _
  · have : Module.Free R ((complex M).X (-q).toNat) := by
      change Module.Free R (term M (-q).toNat)
      infer_instance
    exact Module.Free.of_equiv
      ((complex M).extendXIso embUp (i := (-q).toNat) (by simp; omega)).toLinearEquiv.symm

/-- 整数添字に延長した極小分解の各項は有限生成である。分解全体の有界性は不要。 -/
instance extRes_finite (q : ℤ) : Module.Finite R ((extRes (resolution M)).X q) := by
  by_cases hq : 0 < q
  · have := ModuleCat.subsingleton_of_isZero (extRes_isZero_X (resolution M) q hq)
    infer_instance
  · have : Module.Finite R ((complex M).X (-q).toNat) := by
      change Module.Finite R (term M (-q).toNat)
      infer_instance
    exact Module.Finite.equiv
      ((complex M).extendXIso embUp (i := (-q).toNat) (by simp; omega)).toLinearEquiv.symm

/-- 自由分解の全ての微分は、全ての座標で極大イデアルに値をとる。 -/
lemma d_coordinate_mem (n : ℕ) (x : term M (n + 1))
    (i : Fin (MinimalGenerators.rank (syzygy M n))) :
    d M n x i ∈ IsLocalRing.maximalIdeal R := by
  apply MinimalGenerators.ker_coordinate_mem
  exact (exact_ι_π M n).apply_apply_eq_zero (π M (n + 1) x)

end SerrePositivity.MinimalFreeResolution

end MinimalFreeResolutionPart

section MinimalBettiPart

open CategoryTheory IsLocalRing

namespace SerrePositivity

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]

/-- 等しい有限長をもつ加群の間の全射は単射でもある。 -/
lemma injective_of_surjective_of_length_eq
    {V W : Type u} [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    (f : V →ₗ[R] W) (hf : Function.Surjective f)
    (he : Module.length R V = Module.length R W) (hfin : Module.length R W ≠ ⊤) :
    Function.Injective f := by
  have h := Module.length_eq_add_of_exact (LinearMap.ker f).subtype f
    (Submodule.subtype_injective _) hf (LinearMap.exact_subtype_ker_map f)
  rw [he] at h
  have hz : Module.length R (LinearMap.ker f) = 0 := by
    apply ENat.add_left_injective_of_ne_top hfin
    simpa only [zero_add] using h.symm
  have := Module.length_eq_zero_iff.mp hz
  rw [← LinearMap.ker_eq_bot]
  exact Submodule.eq_bot_of_subsingleton

namespace MinimalFreeResolution

variable [IsLocalRing R] [IsNoetherianRing R] (M : FGModuleCat.{u} R)

/-- 極小被覆の核に移ると、剰余体係数の Tor の次数が一つ下がる。 -/
lemma length_tor_succ (n i : ℕ) :
    Module.length R (TorModule R (i + 1) (syzygy M n) (R ⧸ maximalIdeal R)) =
      Module.length R (TorModule R i (syzygy M (n + 1)) (R ⧸ maximalIdeal R)) := by
  obtain ⟨α, β, δ, hab, hbd, hda, hb⟩ := torModule_longExact_left (R ⧸ maximalIdeal R)
    (ι M n) (π M n) (ι_injective M n) (π_surjective M n) (exact_ι_π M n)
  have hdi : Function.Injective (δ i) := by
    apply (LinearMap.injective_iff_eq_zero_of_exact (hbd i)).mpr
    have := torModule_subsingleton_of_flat (R := R) (term M n) (R ⧸ maximalIdeal R) i
    ext x
    rw [Subsingleton.elim x 0, map_zero]
    rfl
  have hds : Function.Surjective (δ i) := by
    apply (LinearMap.surjective_iff_eq_zero_of_exact (hda i)).mpr
    cases i with
    | zero =>
      have hβ : Function.Injective (β 0) := by
        apply injective_of_surjective_of_length_eq _ hb
        · rw [MinimalGenerators.length_tor_zero (FGModuleCat.of R (term M n)),
            MinimalGenerators.length_tor_zero (syzygy M n), MinimalGenerators.rank_cover]
        · rw [MinimalGenerators.length_tor_zero (syzygy M n)]
          exact ENat.natCast_ne_top _
      exact (LinearMap.injective_iff_eq_zero_of_exact (hab 0)).mp hβ
    | succ i =>
      have := torModule_subsingleton_of_flat (R := R) (term M n) (R ⧸ maximalIdeal R) i
      ext x
      exact Subsingleton.elim _ _
  exact (LinearEquiv.ofBijective (δ i) ⟨hdi, hds⟩).length_eq

/-- 任意の syzygy を始点として、Tor の長さは極小自由分解の対応する項の階数に等しい。 -/
lemma length_tor_syzygy (n i : ℕ) :
    Module.length R (TorModule R i (syzygy M n) (R ⧸ maximalIdeal R)) =
      MinimalGenerators.rank (syzygy M (n + i)) := by
  induction i generalizing n with
  | zero => simpa only [Nat.add_zero] using MinimalGenerators.length_tor_zero (syzygy M n)
  | succ i ih =>
    rw [length_tor_succ]
    simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ih (n + 1)

/-- `Tor_i(M,k)` の長さは、構成した極小自由分解の第 `i` 項の階数である。 -/
lemma length_tor (i : ℕ) :
    Module.length R (TorModule R i M (R ⧸ maximalIdeal R)) =
      MinimalGenerators.rank (syzygy M i) := by
  simpa only [Nat.zero_add, syzygy] using length_tor_syzygy M 0 i

end MinimalFreeResolution
end SerrePositivity

end MinimalBettiPart

section MinimalTruncationPart

open CategoryTheory Limits IsLocalRing

namespace SerrePositivity.MinimalFreeResolution

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable (M : FGModuleCat.{u} R) (l : ℕ)

/-- 極小分解の `[-l,0]` 次を残す、項ごとの切り詰め。 -/
noncomputable def truncated : CochainComplex (ModuleCat.{u} R) ℤ :=
  (extRes (resolution M)).stupidTrunc (ComplexShape.embeddingUpIntGE (-(l : ℤ)))

/-- 切り詰めで残した項は、元の極小自由分解の項と同型。 -/
noncomputable def truncatedXIso (i : ℕ) (hi : i ≤ l) :
    (truncated M l).X (-(i : ℤ)) ≅ term M i :=
  (extRes (resolution M)).stupidTruncXIso (ComplexShape.embeddingUpIntGE (-(l : ℤ)))
    (i := l - i) (by simp; omega) ≪≫
  (complex M).extendXIso embUp (by simp)

lemma truncated_isZero_X (q : ℤ) (hq : q < -(l : ℤ) ∨ 0 < q) :
    IsZero ((truncated M l).X q) := by
  rcases hq with hq | hq
  · apply HomologicalComplex.isZero_stupidTrunc_X
    simpa only [ComplexShape.notMem_range_embeddingUpIntGE_iff] using hq
  · have : (extRes (resolution M)).IsStrictlyLE 0 :=
      (CochainComplex.isStrictlyLE_iff _ _).mpr (isResolutionOf_extRes _).isZero_X
    have : (truncated M l).IsStrictlyLE 0 := by unfold truncated; infer_instance
    exact (truncated M l).isZero_of_isStrictlyLE 0 q hq

instance truncated_free (q : ℤ) : Module.Free R ((truncated M l).X q) := by
  by_cases h : q < -(l : ℤ) ∨ 0 < q
  · have := ModuleCat.subsingleton_of_isZero (truncated_isZero_X M l q h)
    exact Module.Free.of_subsingleton _ _
  · have hq : q = -(((-q).toNat : ℕ) : ℤ) := by omega
    rw [hq]
    exact Module.Free.of_equiv (truncatedXIso M l (-q).toNat (by omega)).toLinearEquiv.symm

instance truncated_finite (q : ℤ) : Module.Finite R ((truncated M l).X q) := by
  by_cases h : q < -(l : ℤ) ∨ 0 < q
  · have := ModuleCat.subsingleton_of_isZero (truncated_isZero_X M l q h)
    infer_instance
  · have hq : q = -(((-q).toNat : ℕ) : ℤ) := by omega
    rw [hq]
    exact Module.Finite.equiv (truncatedXIso M l (-q).toNat (by omega)).toLinearEquiv.symm

/-- 残した項の階数は、同じ次数の Betti 数に一致する。 -/
lemma truncated_finrank (i : ℕ) (hi : i ≤ l) :
    Module.finrank R ((truncated M l).X (-(i : ℤ))) =
      MinimalGenerators.rank (syzygy M i) := by
  rw [(truncatedXIso M l i hi).toLinearEquiv.finrank_eq]
  change Module.finrank R (Fin (MinimalGenerators.rank (syzygy M i)) → R) = _
  simp

lemma truncated_finrank_eq_length_tor (i : ℕ) (hi : i ≤ l) :
    (Module.finrank R ((truncated M l).X (-(i : ℤ))) : ℕ∞) =
      Module.length R (TorModule R i M (R ⧸ maximalIdeal R)) := by
  rw [truncated_finrank M l i hi, length_tor]

/-- 項の同型で移した切り詰めの微分は、元の極小分解の微分そのもの。 -/
lemma truncated_d (i : ℕ) (hi : i + 1 ≤ l) :
    (truncatedXIso M l (i + 1) hi).inv ≫
      (truncated M l).d (-((i + 1 : ℕ) : ℤ)) (-(i : ℤ)) ≫
      (truncatedXIso M l i (by omega)).hom = d M i := by
  unfold truncatedXIso truncated HomologicalComplex.stupidTrunc
  rw [HomologicalComplex.extend_d_eq _ _
    (show (ComplexShape.embeddingUpIntGE (-(l : ℤ))).f (l - (i + 1)) =
      -((i + 1 : ℕ) : ℤ) by simp; omega)
    (show (ComplexShape.embeddingUpIntGE (-(l : ℤ))).f (l - i) = -(i : ℤ) by simp; omega)]
  simp only [HomologicalComplex.stupidTruncXIso, Iso.trans_inv, Iso.trans_hom,
    Category.assoc, Iso.inv_hom_id_assoc]
  rw [HomologicalComplex.restriction_d_eq _ _
    (show (ComplexShape.embeddingUpIntGE (-(l : ℤ))).f (l - (i + 1)) =
      -((i + 1 : ℕ) : ℤ) by simp; omega)
    (show (ComplexShape.embeddingUpIntGE (-(l : ℤ))).f (l - i) = -(i : ℤ) by simp; omega)]
  simp only [HomologicalComplex.restrictionXIso, eqToIso]
  rw [HomologicalComplex.extend_d_eq _ _ (by simp : embUp.f (i + 1) = -((i + 1 : ℕ) : ℤ))
    (by simp : embUp.f i = -(i : ℤ))]
  simp only [resolution_complex, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id, complex_d]

/-- 零次の標準基底に関する微分の座標は、切り詰め後も極大イデアルに入る。 -/
lemma truncated_minimal (x : (truncated M l).X (-1)) (j : Fin (MinimalGenerators.rank M)) :
    (truncatedXIso M l 0 (Nat.zero_le l)).hom ((truncated M l).d (-1) 0 x) j ∈
      maximalIdeal R := by
  by_cases h : 1 ≤ l
  · have hd := truncated_d M l 0 h
    have he := congrArg (fun f ↦ f ((truncatedXIso M l 1 h).hom x) j) hd
    have he' : (truncatedXIso M l 0 (Nat.zero_le l)).hom
        ((truncated M l).d (-1) 0 x) j = d M 0 ((truncatedXIso M l 1 h).hom x) j := by
      simpa using he
    rw [he']
    exact d_coordinate_mem M 0 ((truncatedXIso M l 1 h).hom x) j
  · have hz := truncated_isZero_X M l (-1) (Or.inl (by omega))
    rw [hz.eq_zero_of_src ((truncated M l).d (-1) 0)]
    change (truncatedXIso M l 0 (Nat.zero_le l)).hom.hom 0 j ∈ maximalIdeal R
    rw [map_zero]
    exact (maximalIdeal R).zero_mem

end SerrePositivity.MinimalFreeResolution

end MinimalTruncationPart

section MinimalBoundaryPart

open CategoryTheory Limits HomologicalComplex

namespace SerrePositivity

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]

/-- 加群の消去元の作用は、射影分解で零ホモトピックである。 -/
noncomputable def resolutionScalarNullHomotopy {M : ModuleCat.{u} R}
    (P : ProjectiveResolution M) (r : R) (hr : r • 𝟙 M = 0) :
    Homotopy (r • 𝟙 (extRes P)) 0 := by
  have hc : (r • 𝟙 P.complex) ≫ P.π = 0 := by
    apply HomologicalComplex.Hom.ext
    funext i
    cases i with
    | zero =>
      simp only [smul_f_apply, Linear.smul_comp, Category.id_comp]
      change r • P.π.f 0 = 0
      ext x
      have he := congrArg (fun f : M ⟶ M ↦ f ((P.π.f 0) x)) hr
      exact he
    | succ i =>
      exact (isZero_single_obj_X (ComplexShape.down ℕ) 0 M (i + 1) (by omega)).eq_of_tgt _ _
  have h := (ProjectiveResolution.liftHomotopyZero (P := P) (Q := P) _ hc).extend embUp
  change Homotopy ((embUp.extendFunctor _).map (r • 𝟙 P.complex))
    ((embUp.extendFunctor _).map 0) at h
  simp only [Functor.map_smul, CategoryTheory.Functor.map_id, Functor.map_zero] at h
  exact h

namespace MinimalFreeResolution

variable [IsLocalRing R] [IsNoetherianRing R] (M : FGModuleCat.{u} R) (l : ℕ)

/-- 切り詰めの誤差を担う一項複体。 -/
noncomputable abbrev boundary : CochainComplex (ModuleCat.{u} R) ℤ :=
  TruncationBoundary.boundary (extRes (resolution M)) (-(l : ℤ))

/-- 境界の唯一の項は、極小分解の `l+1` 次の自由項である。 -/
noncomputable def boundaryXIso : (boundary M l).X (-(l : ℤ)) ≅ term M (l + 1) :=
  TruncationBoundary.boundaryXIso _ _ ≪≫
    (complex M).extendXIso embUp (i := l + 1) (by simp; omega)

lemma boundary_isZero_X (q : ℤ) (hq : q ≠ -(l : ℤ)) : IsZero ((boundary M l).X q) :=
  TruncationBoundary.boundary_isZero_X _ _ q hq

instance boundary_free (q : ℤ) : Module.Free R ((boundary M l).X q) := by
  by_cases hq : q = -(l : ℤ)
  · subst q
    exact Module.Free.of_equiv (boundaryXIso M l).toLinearEquiv.symm
  · have := ModuleCat.subsingleton_of_isZero (boundary_isZero_X M l q hq)
    exact Module.Free.of_subsingleton _ _

instance boundary_finite (q : ℤ) : Module.Finite R ((boundary M l).X q) := by
  by_cases hq : q = -(l : ℤ)
  · subst q
    exact Module.Finite.equiv (boundaryXIso M l).toLinearEquiv.symm
  · have := ModuleCat.subsingleton_of_isZero (boundary_isZero_X M l q hq)
    infer_instance

lemma boundary_finrank : Module.finrank R ((boundary M l).X (-(l : ℤ))) =
    MinimalGenerators.rank (syzygy M (l + 1)) := by
  rw [(boundaryXIso M l).toLinearEquiv.finrank_eq]
  change Module.finrank R (Fin (MinimalGenerators.rank (syzygy M (l + 1))) → R) = _
  simp

/-- 切り詰め上の消去元の作用を、直前の自由項を通る射で表す。 -/
lemma scalar_boundary_factorization (r : R) (hr : r • 𝟙 M.obj = 0) :
    ∃ (u : truncated M l ⟶ boundary M l) (v : boundary M l ⟶ truncated M l),
      Nonempty (Homotopy (r • 𝟙 _) (u ≫ v)) :=
  TruncationBoundary.scalar_factorization _ _ r (resolutionScalarNullHomotopy (resolution M) r hr)

end MinimalFreeResolution
end SerrePositivity

end MinimalBoundaryPart
