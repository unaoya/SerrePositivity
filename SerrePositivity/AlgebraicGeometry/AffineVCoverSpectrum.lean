module

public import SerrePositivity.AlgebraicGeometry.AffineVCoverFamily

/-!
概要：付値判定から素スペクトルの全射性と空の族の境界条件を取り出す。
方針：各素点の剰余体を付値環の試験対象とし、忠実平坦拡大の単射性を使う。
規約：Spec の全射性から v 被覆性への逆向きは主張しない。
使われ方：G0 の点の持ち上げと、有限族の積への移送の境界条件。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
universe u
variable {A B : Type u} [CommRing A] [CommRing B]

/-- affine v 被覆は素スペクトル上全射。剰余体で付値判定を試す。 -/
theorem IsAffineVCover.surjectiveSpectrum {f : A →+* B} (hf : IsAffineVCover f) :
    Function.Surjective (PrimeSpectrum.comap f) := by
  intro P
  letI : P.asIdeal.IsPrime := P.isPrime
  obtain ⟨W, hW, hval, e, l, he, hl⟩ :=
    hf (CommRingCat.of P.asIdeal.ResidueField) (algebraMap A P.asIdeal.ResidueField)
  letI : IsDomain W := hW
  refine ⟨⟨RingHom.ker l, RingHom.ker_isPrime l⟩, ?_⟩
  apply PrimeSpectrum.ext
  change Ideal.comap f (RingHom.ker l) = P.asIdeal
  rw [RingHom.comap_ker, hl,
    RingHom.ker_comp_of_injective _ he.injective, Ideal.ker_algebraMap_residueField]

/-- 零環からの射は付値判定を空虚に満たす。零環を定義から除外しない。 -/
theorem isAffineVCover_of_subsingleton [Subsingleton A] (f : A →+* B) : IsAffineVCover f := by
  intro V _ _ k
  have h : (0 : V) = 1 := by
    simpa only [map_zero, map_one] using congrArg k (Subsingleton.elim (0 : A) 1)
  exact (zero_ne_one h).elim

/-- 零環上では空の族を含む任意の有限族が付値判定を満たす。 -/
theorem isAffineVCoverFamily_of_subsingleton [Subsingleton A]
    {ι : Type u} [Finite ι] (B : ι → Type u) [∀ i, CommRing (B i)]
    (f : ∀ i, A →+* B i) : IsAffineVCoverFamily B f :=
  (isAffineVCoverFamily_iff_pi B f).mpr (isAffineVCover_of_subsingleton _)

/-- 非零の基底の有限 v 被覆族には少なくとも一つの成分がある。 -/
theorem IsAffineVCoverFamily.nonempty [Nontrivial A]
    {ι : Type u} [Finite ι] {B : ι → Type u} [∀ i, CommRing (B i)]
    {f : ∀ i, A →+* B i} (hf : IsAffineVCoverFamily B f) : Nonempty ι := by
  obtain ⟨P⟩ := (inferInstance : Nonempty (PrimeSpectrum A))
  obtain ⟨Q, _⟩ := ((isAffineVCoverFamily_iff_pi B f).mp hf).surjectiveSpectrum P
  obtain ⟨i, _, _⟩ := PrimeSpectrum.exists_comap_evalRingHom_eq Q
  exact ⟨i⟩

end SerrePositivity.AlgebraicGeometry
