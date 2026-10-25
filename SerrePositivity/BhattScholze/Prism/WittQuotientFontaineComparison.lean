module

public import SerrePositivity.BhattScholze.Prism.WittQuotientTiltMap

/-! # Witt商の標準Fontaine比較写像

著者公開版Theorem 3.10の比較に使う具体的なδ射と商上の同型。
商の古典的p進完備性は仮定し、台Witt環の同型とは区別する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze
variable (p : ℕ) [Fact p.Prime] (k : Type u) [CommRing k] [CharP k p] [PerfectRing k p]
variable (d : WittVector p k) [Fact (¬ IsUnit (p : WittVector p k ⧸ Ideal.span {d}))]

/-- 標準tilt射が誘導するWitt環からFontaine環への具体的な比較射。 -/
def wittQuotientFontaineMap :
    WittVector p k →+* WittVector p (PreTilt (WittVector p k ⧸ Ideal.span {d}) p) :=
  WittVector.map (wittQuotientTiltMap p k d)

/-- 標準Fontaine比較射は標準δ構造と可換する。 -/
theorem wittQuotientFontaineMap_isDeltaHom :
    (wittDeltaStructure p k).IsDeltaHom
      (wittDeltaStructure p (PreTilt (WittVector p k ⧸ Ideal.span {d}) p))
      (wittQuotientFontaineMap p k d) :=
  wittDeltaStructure_map_isDeltaHom p k (wittQuotientTiltMap p k d)

/-- 比較射でdistinguished元dの像もdistinguished。 -/
theorem wittQuotientFontaineMap_isDistinguished
    (hd : (wittDeltaStructure p k).IsDistinguished d) :
    (wittDeltaStructure p (PreTilt (WittVector p k ⧸ Ideal.span {d}) p)).IsDistinguished
      (wittQuotientFontaineMap p k d d) :=
  (wittQuotientFontaineMap_isDeltaHom p k d).map_isDistinguished hd

variable [IsAdicComplete (Ideal.span {(p : WittVector p k ⧸ Ideal.span {d})})
  (WittVector p k ⧸ Ideal.span {d})]

/-- Fontaine射と標準Witt比較射の合成は、元の標準商射と一致する。
各p冪商でTeichmüller元の一致を使い、古典的p進分離性で結論する。 -/
theorem wittQuotientFontaineMap_comp_fontaineTheta :
    (WittVector.fontaineTheta (WittVector p k ⧸ Ideal.span {d}) p).comp
      (wittQuotientFontaineMap p k d) = Ideal.Quotient.mk (Ideal.span {d}) := by
  let S := WittVector p k ⧸ Ideal.span {d}
  let f := (WittVector.fontaineTheta S p).comp (wittQuotientFontaineMap p k d)
  let g := Ideal.Quotient.mk (Ideal.span {d})
  have ht (x : k) : f (WittVector.teichmuller p x) = g (WittVector.teichmuller p x) := by
    change WittVector.fontaineTheta S p
      (WittVector.map (wittQuotientTiltMap p k d) (WittVector.teichmuller p x)) = _
    rw [WittVector.map_teichmuller, WittVector.fontaineTheta_teichmuller,
      wittQuotientTiltMap_untilt]
  apply RingHom.ext
  intro x
  apply (IsHausdorff.eq_iff_smodEq (I := Ideal.span {(p : S)})).mpr
  intro n
  let q := Ideal.Quotient.mk (Ideal.span {(p : S)} ^ n)
  have hn : IsNilpotent (p : S ⧸ Ideal.span {(p : S)} ^ n) := by
    refine ⟨n, ?_⟩
    rw [← map_natCast q p, ← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_singleton _)) n)
  have hfg : q.comp f = q.comp g :=
    WittVector.eq_of_apply_teichmuller_eq _ _ hn (fun a ↦ congrArg q (ht a))
  rw [smul_eq_mul, Ideal.mul_top]
  apply SModEq.sub_mem.mpr
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change q (f x - g x) = 0
  rw [map_sub]
  exact sub_eq_zero.mpr (RingHom.congr_fun hfg x)

/-- 標準Fontaine核の比較射による逆像は、元の(d)そのもの。 -/
theorem wittQuotientFontaineMap_comap_kernel :
    (RingHom.ker (WittVector.fontaineTheta (WittVector p k ⧸ Ideal.span {d}) p)).comap
      (wittQuotientFontaineMap p k d) = Ideal.span {d} := by
  change RingHom.ker ((WittVector.fontaineTheta (WittVector p k ⧸ Ideal.span {d}) p).comp
    (wittQuotientFontaineMap p k d)) = Ideal.span {d}
  rw [wittQuotientFontaineMap_comp_fontaineTheta]
  exact Ideal.mk_ker

/-- 比較射はdを標準Fontaine核へ送る。 -/
theorem wittQuotientFontaineMap_generator_mem_kernel :
    wittQuotientFontaineMap p k d d ∈
      RingHom.ker (WittVector.fontaineTheta (WittVector p k ⧸ Ideal.span {d}) p) := by
  have h := wittQuotientFontaineMap_comap_kernel p k d
  exact (show d ∈ (RingHom.ker (WittVector.fontaineTheta
    (WittVector p k ⧸ Ideal.span {d}) p)).comap (wittQuotientFontaineMap p k d) by
      rw [h]; exact Ideal.subset_span (Set.mem_singleton _))

/-- 比較射が誘導する具体的な商環の射。 -/
def wittQuotientFontaineQuotientMap :
    (WittVector p k ⧸ Ideal.span {d}) →+*
      (WittVector p (PreTilt (WittVector p k ⧸ Ideal.span {d}) p) ⧸
        RingHom.ker (WittVector.fontaineTheta (WittVector p k ⧸ Ideal.span {d}) p)) :=
  Ideal.quotientMap _ (wittQuotientFontaineMap p k d)
    (by rw [wittQuotientFontaineMap_comap_kernel])

/-- 比較射の誘導商射は代表元に比較射を適用する。 -/
@[simp] theorem wittQuotientFontaineQuotientMap_mk (x : WittVector p k) :
    wittQuotientFontaineQuotientMap p k d (Ideal.Quotient.mk (Ideal.span {d}) x) =
      Ideal.Quotient.mk _ (wittQuotientFontaineMap p k d x) := rfl

/-- 標準商射に対するFontaine第一同型の逆は、比較射の誘導商射に等しい。
全射性は商mod pのFrobenius全射性と古典的p完備性から供給する。 -/
theorem wittQuotientFontaineQuotientMap_eq_inverse :
    wittQuotientFontaineQuotientMap p k d =
      (RingHom.quotientKerEquivOfSurjective
        (surjective_fontaineTheta
          ((wittDeltaStructure_isPerfect p k).quotient_mod_p_frobenius_surjective
            (Ideal.span {d})))).symm.toRingHom := by
  let θ := WittVector.fontaineTheta (WittVector p k ⧸ Ideal.span {d}) p
  have hθ : Function.Surjective θ := surjective_fontaineTheta
    ((wittDeltaStructure_isPerfect p k).quotient_mod_p_frobenius_surjective (Ideal.span {d}))
  let e := RingHom.quotientKerEquivOfSurjective hθ
  apply RingHom.ext
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  apply e.injective
  change e (Ideal.Quotient.mk (RingHom.ker θ) (wittQuotientFontaineMap p k d a)) =
    e (e.symm (Ideal.Quotient.mk (Ideal.span {d}) a))
  rw [RingHom.quotientKerEquivOfSurjective_apply_mk, e.apply_symm_apply]
  exact RingHom.congr_fun (wittQuotientFontaineMap_comp_fontaineTheta p k d) a

/-- 標準比較射の誘導商射は全単射。台Witt環の全単射性は追加結論しない。 -/
theorem wittQuotientFontaineQuotientMap_bijective :
    Function.Bijective (wittQuotientFontaineQuotientMap p k d) := by
  rw [wittQuotientFontaineQuotientMap_eq_inverse]
  exact RingEquiv.bijective _

/-- 元のWitt商と標準Fontaine核による商の具体的な同型。 -/
def wittQuotientFontaineQuotientEquiv :
    (WittVector p k ⧸ Ideal.span {d}) ≃+*
      (WittVector p (PreTilt (WittVector p k ⧸ Ideal.span {d}) p) ⧸
        RingHom.ker (WittVector.fontaineTheta (WittVector p k ⧸ Ideal.span {d}) p)) :=
  RingEquiv.ofBijective (wittQuotientFontaineQuotientMap p k d)
    (wittQuotientFontaineQuotientMap_bijective p k d)

/-- 構成した商同型の台環射は標準比較射の誘導商射。 -/
@[simp] theorem wittQuotientFontaineQuotientEquiv_toRingHom :
    (wittQuotientFontaineQuotientEquiv p k d).toRingHom =
      wittQuotientFontaineQuotientMap p k d := rfl

end SerrePositivity.BhattScholze
