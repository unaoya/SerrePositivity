module

public import SerrePositivity.BhattScholze.Delta.Free.FreeDeltaUniversal
public import SerrePositivity.BhattScholze.Delta.DeltaQuotient

/-! # 自由δ環に関係式を課す普遍性

自由整数δ環のイデアルIのδ閉包による商は、Iを零に送るδ射の普遍対象である。
BS著者版Notation 2.8・Example 2.10の生成元と関係式の代数的構成。
完備化やprismatic envelopeそのものはこのモジュールには含まない。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {σ : Type u} {A : Type v} [CommRing A]

/-- 元族a_sへの評価がIを零に送れば、自由δ環のδ閉包商から、
初期生成元をa_sへ送るδ射が一意に存在する。具体的な商構造・標準写像を明示する。 -/
theorem existsUnique_freeDeltaPresentationHom (D : DeltaStructure p A) (a : σ → A)
    (I : Ideal (FreeDeltaRing σ)) (hI : ∀ r ∈ I, freeDeltaEval D a r = 0) :
    ∃! g : (FreeDeltaRing σ ⧸ (freeDeltaStructure p σ).deltaClosure I) →+* A,
      ((freeDeltaStructure p σ).quotient ((freeDeltaStructure p σ).deltaClosure I)
        ((freeDeltaStructure p σ).isStable_deltaClosure I)).IsDeltaHom D g ∧
      ∀ s : σ, g (Ideal.Quotient.mk ((freeDeltaStructure p σ).deltaClosure I)
        (MvPolynomial.X (s, 0))) = a s := by
  let F := freeDeltaStructure p σ
  let J := F.deltaClosure I
  let Q := F.quotient J (F.isStable_deltaClosure I)
  let q := Ideal.Quotient.mk J
  let f := freeDeltaEval D a
  have hf : F.IsDeltaHom D f := freeDeltaEval_isDeltaHom D a
  have hker : I ≤ RingHom.ker f := fun r hr ↦ hI r hr
  obtain ⟨g, hg, hgu⟩ := F.existsUnique_deltaClosure_quotient_lift I D f hf hker
  refine ⟨g, ⟨hg.2, ?_⟩, ?_⟩
  · intro s
    have h := DFunLike.congr_fun hg.1 (MvPolynomial.X (s, 0))
    exact h.trans (by simp [f])
  · intro k hk
    have hkδ : F.IsDeltaHom D (k.comp q) :=
      hk.1.comp (F.isDeltaHom_quotient_mk J (F.isStable_deltaClosure I))
    have hkgen : ∀ s : σ, (k.comp q) (MvPolynomial.X (s, 0)) = a s := hk.2
    have hfg : ∀ s : σ, f (MvPolynomial.X (s, 0)) = a s := by
      intro s
      simp [f]
    obtain ⟨l, _, hlu⟩ := existsUnique_freeDeltaHom D a
    have hcomp : k.comp q = f :=
      (hlu (k.comp q) ⟨hkδ, hkgen⟩).trans (hlu f ⟨hf, hfg⟩).symm
    exact hgu k ⟨hcomp, hk.1⟩

end SerrePositivity.BhattScholze
