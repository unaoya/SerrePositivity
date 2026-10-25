module

public import SerrePositivity.BhattScholze.Delta.Distinguished.Distinguished

/-! # 主イデアルを持つδ-pairの代数的条件

BS著者公開版Lemma 3.1・3.5の主イデアルでの計算。
prismの導来完備性・Cartier条件・局所化降下をここで定義済みとはしない。
distinguished生成元について必要な理想包含と写像の剛性を証明する。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.BhattScholze.DeltaStructure
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- distinguished元dについてp∈(d^p,φ(d))。φ(d)-d^p=pδ(d)とδ(d)の逆元を使う。
Lemma 3.1の主イデアルの場合の強い包含で、完備性・根基の仮定は不要。 -/
theorem IsDistinguished.p_mem_span_pow {D : DeltaStructure p A} {d : A}
    (hd : D.IsDistinguished d) : (p : A) ∈ Ideal.span {d ^ p, D.frobeniusLift d} := by
  let I := Ideal.span {d ^ p, D.frobeniusLift d}
  have hdp : d ^ p ∈ I := Ideal.subset_span (by simp)
  have hφ : D.frobeniusLift d ∈ I := Ideal.subset_span (by simp)
  have hm : (p : A) * D.delta d ∈ I := by
    have h := I.sub_mem hφ hdp
    simpa only [D.frobeniusLift_apply, add_sub_cancel_left] using h
  obtain ⟨u, hu⟩ := hd
  have h := I.mul_mem_right (↑(u⁻¹) : A) hm
  rw [← hu, mul_assoc, Units.mul_inv, mul_one] at h
  exact h

/-- d,pがJacobson根基に属せば、distinguished性はp∈(d^p,φ(d))と同値。
弱い包含の判定Lemma 2.25と、主イデアルの強い包含を組み合わせる。 -/
theorem isDistinguished_iff_p_mem_span_pow (D : DeltaStructure p A) (d : A)
    (hdr : d ∈ Ideal.jacobson (⊥ : Ideal A))
    (hpr : (p : A) ∈ Ideal.jacobson (⊥ : Ideal A)) :
    D.IsDistinguished d ↔ (p : A) ∈ Ideal.span {d ^ p, D.frobeniusLift d} := by
  refine ⟨fun h ↦ h.p_mem_span_pow, fun h ↦ ?_⟩
  apply D.isDistinguished_of_p_mem_span d hdr hpr
  apply (show Ideal.span {d ^ p, D.frobeniusLift d} ≤
      Ideal.span {d, D.frobeniusLift d} from ?_) h
  apply Ideal.span_le.mpr
  intro x hx
  rcases Set.mem_insert_iff.mp hx with rfl | hx
  · exact (Ideal.span {d, D.frobeniusLift d}).pow_mem_of_mem
      (Ideal.subset_span (by simp)) p (Fact.out : p.Prime).pos
  · rw [Set.mem_singleton_iff.mp hx]
    exact Ideal.subset_span (by simp)

/-- δ射がdistinguished生成元dを(e)へ送れば、その主イデアルの像は(e)全体。
e,pが終域のJacobson根基に属する仮定で因子判定を使う。
Lemma 3.5の局所的な計算であり、一般prismの降下までは含まない。 -/
theorem IsDeltaHom.map_span_eq_of_distinguished_of_mem_span
    {B : Type v} [CommRing B] {D : DeltaStructure p A} {E : DeltaStructure p B}
    {f : A →+* B} (hf : D.IsDeltaHom E f) {d : A} {e : B}
    (hd : D.IsDistinguished d) (he : f d ∈ Ideal.span {e})
    (her : e ∈ Ideal.jacobson (⊥ : Ideal B))
    (hpr : (p : B) ∈ Ideal.jacobson (⊥ : Ideal B)) :
    (Ideal.span {d}).map f = Ideal.span {e} := by
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp he
  have hfd := hf.map_isDistinguished hd
  rw [hr] at hfd
  have hru := (E.isDistinguished_factor e r hfd her hpr).2
  rw [Ideal.map_span, Set.image_singleton, hr, Ideal.span_singleton_mul_right_unit hru]

end SerrePositivity.BhattScholze.DeltaStructure
