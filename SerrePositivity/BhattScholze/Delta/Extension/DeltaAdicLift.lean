module

public import SerrePositivity.BhattScholze.Delta.Extension.DeltaAdicCompletion
public import Mathlib.RingTheory.AdicCompletion.RingHom
public import SerrePositivity.CommutativeAlgebra.AdicCompletionExt

/-! # 古典的完備化からのδ射の延長

有限生成I、p∈I、J進分離したδ終域への基底δ射を扱う。
Mathlibの完備化・環射の持上げと共通評価核APIを再利用する。
導来完備化との比較やProp 7.2の超限構成を代替しない。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.BhattScholze.DeltaStructure
variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R]
variable {A : Type v} [CommRing A]

/-- 基底δ射を延長する環射は、終域がJ進分離していればδ射。
源の有限生成性とf(I)⊂Jを公開仮定に明示する。 -/
theorem IsDeltaHom.adicCompletion_extension {D : DeltaStructure p R}
    {E : DeltaStructure p A} {f : R →+* A} (hf : D.IsDeltaHom E f)
    (I : Ideal R) (hp : (p : R) ∈ I) (hI : I.FG) (J : Ideal A) [IsHausdorff J A]
    (hIJ : I.map f ≤ J) (g : AdicCompletion I R →+* A)
    (hg : g.comp (algebraMap R (AdicCompletion I R)) = f) :
    (D.adicCompletion I hp).IsDeltaHom E g := by
  let j := algebraMap R (AdicCompletion I R)
  let K := I.map j
  have hK : K.map g ≤ J := by
    change (I.map j).map g ≤ J
    rw [Ideal.map_map, hg]
    exact hIJ
  have hmap (n : ℕ) (z : AdicCompletion I R) (hz : z ∈ K ^ n) : g z ∈ J ^ n := by
    have h := Ideal.mem_map_of_mem g hz
    rw [Ideal.map_pow] at h
    exact Ideal.pow_right_mono hK n h
  have hpK : (p : AdicCompletion I R) ∈ K := by
    simpa only [map_natCast] using Ideal.mem_map_of_mem j hp
  have hpJ : (p : A) ∈ J := by
    simpa only [map_natCast] using hIJ (Ideal.mem_map_of_mem f hp)
  have hgj (r : R) : g (j r) = f r := DFunLike.congr_fun hg r
  intro x
  apply (IsHausdorff.eq_iff_smodEq (I := J)).mpr
  intro n
  apply SModEq.sub_mem.mpr
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I (n + 1) x)
  have hx : x - j r ∈ K ^ (n + 1) := by
    rw [← SerrePositivity.adicCompletion_ker_eval_eq_pow_map I hI]
    change AdicCompletion.evalₐ I (n + 1) (x - j r) = 0
    rw [map_sub, ← hr]
    change Ideal.Quotient.mk _ r - Ideal.Quotient.mk _ r = 0
    exact sub_self _
  have hl := hmap n _ ((D.adicCompletion I hp).delta_sub_mem_pow K hpK n x (j r) hx)
  rw [map_sub, ← D.isDeltaHom_adicCompletion I hp r, hgj] at hl
  have hx' := hmap (n + 1) _ hx
  rw [map_sub, hgj] at hx'
  have hr' := E.delta_sub_mem_pow J hpJ n (g x) (f r) hx'
  rw [← hf r] at hr'
  have h := (J ^ n).sub_mem hl hr'
  simpa only [sub_sub_sub_cancel_right, smul_eq_mul, Ideal.mul_top] using h

/-- 完備化から分離した終域への基底射の延長は一意。
δ射の公開普遍性に使う、具体的な基底射に相対的な外延性。 -/
theorem adicCompletion_extension_unique (I : Ideal R) (hI : I.FG) (J : Ideal A)
    [IsHausdorff J A] (f : R →+* A) (hIJ : I.map f ≤ J)
    (g k : AdicCompletion I R →+* A)
    (hg : g.comp (algebraMap R (AdicCompletion I R)) = f)
    (hk : k.comp (algebraMap R (AdicCompletion I R)) = f) : g = k := by
  let := f.toAlgebra
  let : IsHausdorff I A := IsHausdorff.of_map hIJ
  let ga : AdicCompletion I R →ₐ[R] A :=
    { g with commutes' := fun r ↦ DFunLike.congr_fun hg r }
  let ka : AdicCompletion I R →ₐ[R] A :=
    { k with commutes' := fun r ↦ DFunLike.congr_fun hk r }
  have he : ga.toLinearMap = ka.toLinearMap :=
    SerrePositivity.adicCompletion_linearMap_ext_of_of I hI _ _ (by
      apply LinearMap.ext
      intro r
      exact (DFunLike.congr_fun hg r).trans (DFunLike.congr_fun hk r).symm)
  ext x
  exact DFunLike.congr_fun he x

/-- pを含む有限生成Iの古典的完備化から、J進完備δ環への一意な延長。
具体的な基底δ射fとf(I)⊂Jを仮定する。 -/
theorem existsUnique_adicCompletion_lift (D : DeltaStructure p R) (E : DeltaStructure p A)
    (I : Ideal R) (hp : (p : R) ∈ I) (hI : I.FG) (J : Ideal A) [IsAdicComplete J A]
    (f : R →+* A) (hf : D.IsDeltaHom E f) (hIJ : I.map f ≤ J) :
    ∃! g : AdicCompletion I R →+* A,
      g.comp (algebraMap R (AdicCompletion I R)) = f ∧
        (D.adicCompletion I hp).IsDeltaHom E g := by
  let q (n : ℕ) : R ⧸ I ^ n →+* A ⧸ J ^ n :=
    Ideal.Quotient.lift (I ^ n) ((Ideal.Quotient.mk (J ^ n)).comp f) (by
      intro r hr
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      have h := Ideal.mem_map_of_mem f hr
      rw [Ideal.map_pow] at h
      exact Ideal.pow_right_mono hIJ n h)
  let F (n : ℕ) : AdicCompletion I R →+* A ⧸ J ^ n :=
    (q n).comp (AdicCompletion.evalₐ I n).toRingHom
  have hF {m n : ℕ} (hmn : m ≤ n) :
      (Ideal.Quotient.factorPow J hmn).comp (F n) = F m := by
    apply RingHom.ext
    intro x
    obtain ⟨a, rfl⟩ := AdicCompletion.mk_surjective I R x
    simp only [F, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, q]
    change Ideal.Quotient.mk (J ^ m) (f (a n)) = Ideal.Quotient.mk (J ^ m) (f (a m))
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
    have ha : a n - a m ∈ I ^ m := by
      simpa [SModEq.sub_mem, smul_eq_mul] using (a.property hmn).symm
    have h := Ideal.mem_map_of_mem f ha
    rw [Ideal.map_pow, map_sub] at h
    exact Ideal.pow_right_mono hIJ m h
  let g := IsAdicComplete.liftRingHom J F (fun h ↦ hF h)
  have hg : g.comp (algebraMap R (AdicCompletion I R)) = f := by
    apply RingHom.ext
    intro r
    apply (IsHausdorff.eq_iff_smodEq (I := J)).mpr
    intro n
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
    change Ideal.Quotient.mk (J ^ n) (g (algebraMap R (AdicCompletion I R) r)) =
      Ideal.Quotient.mk (J ^ n) (f r)
    rw [IsAdicComplete.mk_liftRingHom]
    change q n (AdicCompletion.evalₐ I n (AdicCompletion.of I R r)) = _
    rw [AdicCompletion.evalₐ_of]
    rfl
  refine ⟨g, ⟨hg, hf.adicCompletion_extension I hp hI J hIJ g hg⟩, ?_⟩
  intro k hk
  exact adicCompletion_extension_unique I hI J f hIJ k g hk.1 hg

end SerrePositivity.BhattScholze.DeltaStructure
