module

public import SerrePositivity.BhattScholze.Prism.Perfection.PCompletedDeltaDivision
public import SerrePositivity.BhattScholze.Prism.Basic.PerfectOrientedPrism

/-! # p進完備δ除算完全化のd商と完全prismへの延長

著者公開版Prop 7.2とCor 7.3に向けた具体的な環・標準写像・普遍性の部分定理。
任意の基底イデアルJを扱うが、d商のperfectoid性とIsPerfectoidizationは未結論。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R]

/-- Jの全元の像は、具体的な候補環でdの像の主イデアルに含まれる。 -/
theorem pCompletedDeltaDivisionMap_ideal_le_span (D : DeltaStructure p R) (d : R) (J : Ideal R) :
    J ≤ (Ideal.span {pCompletedDeltaDivisionMap D d (fun x : J ↦ (x : R)) d}).comap
      (pCompletedDeltaDivisionMap D d (fun x : J ↦ (x : R))) := by
  intro x hx
  apply Ideal.mem_span_singleton.mpr
  exact pCompletedDeltaDivisionMap_dvd D d (fun x : J ↦ (x : R)) ⟨x, hx⟩

/-- 任意の基底商R/Jから、具体的な候補のmod d商への標準射。 -/
def pCompletedDeltaDivisionQuotientMap (D : DeltaStructure p R) (d : R) (J : Ideal R) :
    R ⧸ J →+*
      (PCompletedDeltaDivision D d (fun x : J ↦ (x : R)) ⧸
        Ideal.span {pCompletedDeltaDivisionMap D d (fun x : J ↦ (x : R)) d}) :=
  Ideal.Quotient.lift J
    ((Ideal.Quotient.mk _).comp (pCompletedDeltaDivisionMap D d (fun x : J ↦ (x : R))))
    (by
      intro x hx
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      exact pCompletedDeltaDivisionMap_ideal_le_span D d J hx)

/-- 基底商への標準射は、代表元に候補への標準射を適用してmod dへ送る。 -/
@[simp] theorem pCompletedDeltaDivisionQuotientMap_mk
    (D : DeltaStructure p R) (d : R) (J : Ideal R) (x : R) :
    pCompletedDeltaDivisionQuotientMap D d J (Ideal.Quotient.mk J x) =
      Ideal.Quotient.mk _ (pCompletedDeltaDivisionMap D d (fun x : J ↦ (x : R)) x) := rfl

/-- 完全prismへの基底δ射でdとJがprismイデアルへ入れば、候補環からの一意延長が存在。
終域の正則性・p完備性・Jの像の可除性をprismの既存APIで内部に供給する。 -/
theorem existsUnique_pCompletedDeltaDivisionHom_to_perfectPrism
    {A : Type v} [CommRing A] (D : DeltaStructure p R) (d : R) (hd : D.IsDistinguished d)
    (J : Ideal R) (Q : OrientedPrism p A) (hQ : Q.deltaStructure.IsPerfect)
    (f : R →+* A) (hf : D.IsDeltaHom Q.deltaStructure f)
    (hdf : f d ∈ Q.ideal) (hJ : J ≤ Q.ideal.comap f) :
    ∃! g : PCompletedDeltaDivision D d (fun x : J ↦ (x : R)) →+* A,
      (pCompletedDeltaDivisionStructure D d (fun x : J ↦ (x : R))).IsDeltaHom Q.deltaStructure g ∧
        g.comp (pCompletedDeltaDivisionMap D d (fun x : J ↦ (x : R))) = f := by
  let := Q.isAdicComplete_p_of_perfect hQ
  let := Q.isAdicComplete_generator
  have hspan : (Ideal.span {d}).map f = Q.ideal :=
    hf.map_span_eq_of_distinguished_of_mem_span hd hdf
      (IsAdicComplete.le_jacobson_bot (Ideal.span {Q.generator}) (Ideal.subset_span (by simp)))
      (IsAdicComplete.le_jacobson_bot (Ideal.span {(p : A)}) (Ideal.subset_span (by simp)))
  have ha (x : J) : f d ∣ f (x : R) := by
    apply Ideal.mem_span_singleton.mp
    have hx := hJ x.property
    rw [← hspan, Ideal.map_span, Set.image_singleton] at hx
    exact hx
  exact existsUnique_pCompletedDeltaDivisionHom D Q.deltaStructure hQ d hd
    (fun x : J ↦ (x : R)) f hf ha

section Lift
variable {A : Type v} [CommRing A] (D : DeltaStructure p R) (d : R) (hd : D.IsDistinguished d)
variable (J : Ideal R) (Q : OrientedPrism p A) (hQ : Q.deltaStructure.IsPerfect)
variable (f : R →+* A) (hf : D.IsDeltaHom Q.deltaStructure f)
variable (hdf : f d ∈ Q.ideal) (hJ : J ≤ Q.ideal.comap f)

/-- 任意の完全prismへの一意な具体的延長環射。候補環にはprism性を仮定しない。 -/
def pCompletedDeltaDivisionPrismLift :
    PCompletedDeltaDivision D d (fun x : J ↦ (x : R)) →+* A :=
  (existsUnique_pCompletedDeltaDivisionHom_to_perfectPrism D d hd J Q hQ f hf hdf hJ).choose

/-- 選んだ延長環射はδ射。 -/
theorem pCompletedDeltaDivisionPrismLift_isDeltaHom :
    (pCompletedDeltaDivisionStructure D d (fun x : J ↦ (x : R))).IsDeltaHom Q.deltaStructure
      (pCompletedDeltaDivisionPrismLift D d hd J Q hQ f hf hdf hJ) :=
  (existsUnique_pCompletedDeltaDivisionHom_to_perfectPrism D d hd J Q hQ
    f hf hdf hJ).choose_spec.1.1

/-- 選んだ延長環射は標準基底射を延長する。 -/
@[simp] theorem pCompletedDeltaDivisionPrismLift_comp_map :
    (pCompletedDeltaDivisionPrismLift D d hd J Q hQ f hf hdf hJ).comp
      (pCompletedDeltaDivisionMap D d (fun x : J ↦ (x : R))) = f :=
  (existsUnique_pCompletedDeltaDivisionHom_to_perfectPrism D d hd J Q hQ
    f hf hdf hJ).choose_spec.1.2

/-- 候補のmod d商から完全prismの標準商への具体的な誘導射。 -/
def pCompletedDeltaDivisionPrismQuotientMap :
    (PCompletedDeltaDivision D d (fun x : J ↦ (x : R)) ⧸
      Ideal.span {pCompletedDeltaDivisionMap D d (fun x : J ↦ (x : R)) d}) →+* A ⧸ Q.ideal :=
  Ideal.quotientMap Q.ideal (pCompletedDeltaDivisionPrismLift D d hd J Q hQ f hf hdf hJ) (by
    apply (Ideal.span_singleton_le_iff_mem _).mpr
    change pCompletedDeltaDivisionPrismLift D d hd J Q hQ f hf hdf hJ
      (pCompletedDeltaDivisionMap D d (fun x : J ↦ (x : R)) d) ∈ Q.ideal
    rw [show pCompletedDeltaDivisionPrismLift D d hd J Q hQ f hf hdf hJ
      (pCompletedDeltaDivisionMap D d (fun x : J ↦ (x : R)) d) = f d from
        RingHom.congr_fun (pCompletedDeltaDivisionPrismLift_comp_map D d hd J Q hQ f hf hdf hJ) d]
    exact hdf)

/-- 候補を経由した基底商の写像は、元のfによる標準商射に一致する。 -/
theorem pCompletedDeltaDivisionPrismQuotientMap_comp :
    (pCompletedDeltaDivisionPrismQuotientMap D d hd J Q hQ f hf hdf hJ).comp
      (pCompletedDeltaDivisionQuotientMap D d J) = Ideal.quotientMap Q.ideal f hJ := by
  apply RingHom.ext
  intro x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  change Ideal.Quotient.mk Q.ideal (pCompletedDeltaDivisionPrismLift D d hd J Q hQ f hf hdf hJ
    (pCompletedDeltaDivisionMap D d (fun x : J ↦ (x : R)) r)) = Ideal.Quotient.mk Q.ideal (f r)
  rw [show pCompletedDeltaDivisionPrismLift D d hd J Q hQ f hf hdf hJ
    (pCompletedDeltaDivisionMap D d (fun x : J ↦ (x : R)) r) = f r from
      RingHom.congr_fun (pCompletedDeltaDivisionPrismLift_comp_map D d hd J Q hQ f hf hdf hJ) r]

end Lift
end SerrePositivity.BhattScholze
