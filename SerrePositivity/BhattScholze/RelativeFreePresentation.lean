module

public import SerrePositivity.BhattScholze.RelativeFreeUniversal

/-! # 基底δ環上の生成元と関係式

相対自由δ環のイデアルのδ閉包で割り、指定した関係式と基底δ射を満たす
普遍δ射を構成する。BS著者版Notation 2.8・Example 2.10の相対構成。
-/

@[expose] public noncomputable section
universe u v w
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R]
    {σ : Type v} {A : Type w} [CommRing A]

/-- 基底δ射fと元族a_sへの評価がIを零に送れば、相対自由δ環のδ閉包商から
基底上f、初期生成元上a_sとなるδ射が一意に存在する。
具体的な商・商δ構造・基底の標準射との両立を公開型に含める。 -/
theorem existsUnique_relativeFreePresentationHom (D : DeltaStructure p R)
    (E : DeltaStructure p A) (f : R →+* A) (hf : D.IsDeltaHom E f) (a : σ → A)
    (I : Ideal (RelativeFreeDeltaRing (R := R) σ))
    (hI : ∀ r ∈ I, relativeFreeDeltaEval E f a r = 0) :
    ∃! g : (RelativeFreeDeltaRing (R := R) σ ⧸
        (relativeFreeDeltaStructure σ D).deltaClosure I) →+* A,
      ((relativeFreeDeltaStructure σ D).quotient
        ((relativeFreeDeltaStructure σ D).deltaClosure I)
        ((relativeFreeDeltaStructure σ D).isStable_deltaClosure I)).IsDeltaHom E g ∧
      g.comp ((Ideal.Quotient.mk ((relativeFreeDeltaStructure σ D).deltaClosure I)).comp
        MvPolynomial.C) = f ∧
      ∀ s : σ, g (Ideal.Quotient.mk ((relativeFreeDeltaStructure σ D).deltaClosure I)
        (MvPolynomial.X (s, 0))) = a s := by
  let F := relativeFreeDeltaStructure σ D
  let J := F.deltaClosure I
  let q := Ideal.Quotient.mk J
  let t := relativeFreeDeltaEval E f a
  have ht : F.IsDeltaHom E t := relativeFreeDeltaEval_isDeltaHom D E f hf a
  have htC : t.comp MvPolynomial.C = f := by
    ext r
    simp [t]
  have htgen : ∀ s : σ, t (MvPolynomial.X (s, 0)) = a s := by
    intro s
    simp [t]
  have hker : I ≤ RingHom.ker t := fun r hr ↦ hI r hr
  obtain ⟨g, hg, hgu⟩ := F.existsUnique_deltaClosure_quotient_lift I E t ht hker
  refine ⟨g, ⟨hg.2, ?_, ?_⟩, ?_⟩
  · change g.comp (q.comp MvPolynomial.C) = f
    rw [← RingHom.comp_assoc, hg.1, htC]
  · intro s
    exact (DFunLike.congr_fun hg.1 (MvPolynomial.X (s, 0))).trans (htgen s)
  · intro k hk
    have hkδ : F.IsDeltaHom E (k.comp q) :=
      hk.1.comp (F.isDeltaHom_quotient_mk J (F.isStable_deltaClosure I))
    have hkC : (k.comp q).comp MvPolynomial.C = f := by
      rw [RingHom.comp_assoc]
      exact hk.2.1
    have hkgen : ∀ s : σ, (k.comp q) (MvPolynomial.X (s, 0)) = a s := hk.2.2
    obtain ⟨l, _, hlu⟩ := existsUnique_relativeFreeDeltaHom D E f hf a
    have hcomp : k.comp q = t :=
      (hlu (k.comp q) ⟨hkδ, hkC, hkgen⟩).trans (hlu t ⟨ht, htC, htgen⟩).symm
    exact hgu k ⟨hcomp, hk.1⟩

end SerrePositivity.BhattScholze
