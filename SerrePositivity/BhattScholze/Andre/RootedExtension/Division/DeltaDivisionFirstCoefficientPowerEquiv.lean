module

public import SerrePositivity.BhattScholze.Delta.Division.Relations.DeltaDivisionFirstResiduePowerPresentation
public import SerrePositivity.BhattScholze.Andre.RootedExtension.MonicPowerFamilyPresentation
public import SerrePositivity.BhattScholze.Andre.RootedExtension.MonicPowerFamilyBaseQuotient

/-! # 初期係数商と通常根添加環の比較射

A/(p,d,a_s)を明示し、初期多項式商と通常根添加環の具体的な同型を構成する。
さらに実際の初期δ剰余を後続変数の多項式環として表示する。
-/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- 初期剰余の基底係数イデアル。a_sの消滅を含む。 -/
def deltaDivisionFirstBaseIdeal (d : A) (a : σ → A) : Ideal A :=
  Ideal.span {(p : A), d} ⊔ Ideal.span (Set.range a)

/-- 初期根添加の係数族を適切な基底商へ送る。 -/
def deltaDivisionFirstPowerCoefficients (D : DeltaStructure p A) (d : A) (a : σ → A)
    (u : Aˣ) : σ → A ⧸ deltaDivisionFirstBaseIdeal (p := p) d a :=
  fun s => Ideal.Quotient.mk _ ((u⁻¹ : Aˣ) * D.delta (a s))

/-- 適切な基底商上の初期通常根添加環。 -/
abbrev DeltaDivisionFirstPowerCover (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) :=
  MonicPowerFamilyCover p σ (A ⧸ deltaDivisionFirstBaseIdeal (p := p) d a)
    (deltaDivisionFirstPowerCoefficients D d a u)

/-- 初期多項式から、基底商上の具体的な根への評価射。 -/
def deltaDivisionFirstPowerEvaluation (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) :
    MvPolynomial σ A →+* DeltaDivisionFirstPowerCover D d a u :=
  MvPolynomial.eval₂Hom
    ((algebraMap (A ⧸ deltaDivisionFirstBaseIdeal (p := p) d a)
      (DeltaDivisionFirstPowerCover D d a u)).comp (Ideal.Quotient.mk _))
    (monicPowerFamilyRoot p σ _ (deltaDivisionFirstPowerCoefficients D d a u))

/-- 根への評価射の係数上の式。 -/
@[simp] theorem deltaDivisionFirstPowerEvaluation_C
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) (r : A) :
    deltaDivisionFirstPowerEvaluation D d a u (MvPolynomial.C r) =
      algebraMap (A ⧸ deltaDivisionFirstBaseIdeal (p := p) d a)
        (DeltaDivisionFirstPowerCover D d a u) (Ideal.Quotient.mk _ r) := by
  change MvPolynomial.eval₂Hom _ _ (MvPolynomial.C r) = _
  rw [MvPolynomial.eval₂Hom_C]
  rfl

/-- 根への評価射の変数上の式。 -/
@[simp] theorem deltaDivisionFirstPowerEvaluation_X
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) (s : σ) :
    deltaDivisionFirstPowerEvaluation D d a u (MvPolynomial.X s) =
      monicPowerFamilyRoot p σ _ (deltaDivisionFirstPowerCoefficients D d a u) s := by
  change MvPolynomial.eval₂Hom _ _ (MvPolynomial.X s) = _
  rw [MvPolynomial.eval₂Hom_X']

/-- 初期係数イデアルは基底イデアルと指定モニック冪関係式の和。 -/
theorem deltaDivisionFirstPolynomialIdeal_eq_base_sup
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) :
    deltaDivisionFirstPolynomialIdeal D d a u =
      (deltaDivisionFirstBaseIdeal (p := p) d a).map
        (MvPolynomial.C : A →+* MvPolynomial σ A) ⊔
      monicPowerFamilyRelationIdeal p σ A (fun s => (u⁻¹ : Aˣ) * D.delta (a s)) := by
  simp only [deltaDivisionFirstPolynomialIdeal, deltaDivisionFirstBaseIdeal,
    monicPowerFamilyRelationIdeal, Ideal.map_sup, Ideal.map_span,
    Set.image_pair, ← Set.range_comp', map_natCast]

/-- 従来の根評価射は、一般の係数商比較の標準商元上の射と一致する。 -/
theorem deltaDivisionFirstPowerEvaluation_eq_baseQuotient
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) (x : MvPolynomial σ A) :
    deltaDivisionFirstPowerEvaluation D d a u x =
      monicPowerFamilyBaseQuotientEquiv p σ A
        (deltaDivisionFirstBaseIdeal (p := p) d a) (fun s => (u⁻¹ : Aˣ) * D.delta (a s))
        (Ideal.Quotient.mk _ x) := by
  rw [monicPowerFamilyBaseQuotientEquiv_mk]
  change MvPolynomial.eval₂Hom _ _ x =
    MvPolynomial.eval₂Hom _ _ (MvPolynomial.map (Ideal.Quotient.mk _) x)
  rw [MvPolynomial.eval₂Hom_map_hom]
  rfl

/-- 初期根への評価射は、実際の初期係数多項式イデアルを消す。 -/
theorem deltaDivisionFirstPowerEvaluation_kills
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) :
    ∀ x ∈ deltaDivisionFirstPolynomialIdeal D d a u,
      deltaDivisionFirstPowerEvaluation D d a u x = 0 := by
  intro x hx
  rw [deltaDivisionFirstPolynomialIdeal_eq_base_sup] at hx
  rw [deltaDivisionFirstPowerEvaluation_eq_baseQuotient,
    Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]

/-- 初期多項式商から適切な基底商上の通常根添加環への写像。 -/
def deltaDivisionFirstPolynomialToPowerCover
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) :
    MvPolynomial σ A ⧸ deltaDivisionFirstPolynomialIdeal D d a u →+*
      DeltaDivisionFirstPowerCover D d a u :=
  Ideal.Quotient.lift _ (deltaDivisionFirstPowerEvaluation D d a u)
    (deltaDivisionFirstPowerEvaluation_kills D d a u)

/-- 比較射は標準商射上で指定した評価射と一致する。 -/
theorem deltaDivisionFirstPolynomialToPowerCover_mk
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) (x : MvPolynomial σ A) :
    deltaDivisionFirstPolynomialToPowerCover D d a u
      (Ideal.Quotient.mk _ x) = deltaDivisionFirstPowerEvaluation D d a u x := rfl

/-- 比較射は元の係数を基底商の標準像へ送る。 -/
@[simp] theorem deltaDivisionFirstPolynomialToPowerCover_coeff
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) (r : A) :
    deltaDivisionFirstPolynomialToPowerCover D d a u (Ideal.Quotient.mk _ (MvPolynomial.C r)) =
      algebraMap (A ⧸ deltaDivisionFirstBaseIdeal (p := p) d a)
        (DeltaDivisionFirstPowerCover D d a u) (Ideal.Quotient.mk _ r) := by
  change MvPolynomial.eval₂Hom _ _ (MvPolynomial.C r) = _
  rw [MvPolynomial.eval₂Hom_C]
  rfl

/-- 比較射は初期変数を通常根添加環の指定根へ送る。 -/
@[simp] theorem deltaDivisionFirstPolynomialToPowerCover_root
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) (s : σ) :
    deltaDivisionFirstPolynomialToPowerCover D d a u (Ideal.Quotient.mk _ (MvPolynomial.X s)) =
      monicPowerFamilyRoot p σ _ (deltaDivisionFirstPowerCoefficients D d a u) s := by
  change MvPolynomial.eval₂Hom _ _ (MvPolynomial.X s) = _
  rw [MvPolynomial.eval₂Hom_X']

/-- 従来の標準商射は、一般のモニック係数商表示によって全射。 -/
theorem deltaDivisionFirstPolynomialToPowerCover_surjective
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) :
    Function.Surjective (deltaDivisionFirstPolynomialToPowerCover D d a u) := by
  let e := monicPowerFamilyBaseQuotientEquiv p σ A
    (deltaDivisionFirstBaseIdeal (p := p) d a) (fun s => (u⁻¹ : Aˣ) * D.delta (a s))
  intro z
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (e.symm z)
  refine ⟨Ideal.Quotient.mk _ x, ?_⟩
  change deltaDivisionFirstPowerEvaluation D d a u x = z
  rw [deltaDivisionFirstPowerEvaluation_eq_baseQuotient]
  change e (Ideal.Quotient.mk _ x) = z
  rw [hx, e.apply_symm_apply]

/-- 基底係数イデアルの多項式環への像は初期関係式イデアルに含まれる。 -/
theorem deltaDivisionFirstBaseIdeal_map_C_le
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) :
    (deltaDivisionFirstBaseIdeal (p := p) d a).map
      (MvPolynomial.C : A →+* MvPolynomial σ A) ≤ deltaDivisionFirstPolynomialIdeal D d a u := by
  rw [deltaDivisionFirstPolynomialIdeal_eq_base_sup]
  exact le_sup_left

/-- 適切な基底商から初期多項式商への標準係数射。 -/
def deltaDivisionFirstBaseToPolynomialQuotient
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) :
    A ⧸ deltaDivisionFirstBaseIdeal (p := p) d a →+*
      MvPolynomial σ A ⧸ deltaDivisionFirstPolynomialIdeal D d a u :=
  Ideal.Quotient.lift _
    ((Ideal.Quotient.mk (deltaDivisionFirstPolynomialIdeal D d a u)).comp MvPolynomial.C)
    (fun _ hx => Ideal.Quotient.eq_zero_iff_mem.mpr
      (deltaDivisionFirstBaseIdeal_map_C_le D d a u (Ideal.mem_map_of_mem _ hx)))

/-- 逆向き係数射は元の係数の標準像を保つ。 -/
@[simp] theorem deltaDivisionFirstBaseToPolynomialQuotient_mk
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) (r : A) :
    deltaDivisionFirstBaseToPolynomialQuotient D d a u (Ideal.Quotient.mk _ r) =
      Ideal.Quotient.mk _ (MvPolynomial.C r) := rfl

/-- 初期多項式商の変数は基底商上の指定根である。 -/
theorem deltaDivisionFirstPolynomialQuotient_root_pow
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) (s : σ) :
    (Ideal.Quotient.mk (deltaDivisionFirstPolynomialIdeal D d a u) (MvPolynomial.X s)) ^ p =
      deltaDivisionFirstBaseToPolynomialQuotient D d a u
        (deltaDivisionFirstPowerCoefficients D d a u s) := by
  have hm : Ideal.span (Set.range fun t => MvPolynomial.X t ^ p -
      MvPolynomial.C ((u⁻¹ : Aˣ) * D.delta (a t))) ≤
      deltaDivisionFirstPolynomialIdeal D d a u := le_sup_right
  have h := Ideal.Quotient.eq_zero_iff_mem.mpr (hm (Ideal.subset_span (Set.mem_range_self s)))
  rw [map_sub, map_pow, sub_eq_zero] at h
  exact h

/-- 指定根の普遍性による、通常根添加環から初期多項式商への逆向きの射。 -/
def deltaDivisionFirstPowerCoverToPolynomial
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) :
    DeltaDivisionFirstPowerCover D d a u →+*
      MvPolynomial σ A ⧸ deltaDivisionFirstPolynomialIdeal D d a u :=
  monicPowerFamilyCoverMap p σ _ (deltaDivisionFirstPowerCoefficients D d a u)
    (deltaDivisionFirstBaseToPolynomialQuotient D d a u)
    (fun s => Ideal.Quotient.mk _ (MvPolynomial.X s))
    (deltaDivisionFirstPolynomialQuotient_root_pow D d a u)

/-- 逆向き比較射は元の係数を保つ。 -/
@[simp] theorem deltaDivisionFirstPowerCoverToPolynomial_coeff
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) (r : A) :
    deltaDivisionFirstPowerCoverToPolynomial D d a u
      (algebraMap (A ⧸ deltaDivisionFirstBaseIdeal (p := p) d a)
        (DeltaDivisionFirstPowerCover D d a u) (Ideal.Quotient.mk _ r)) =
      Ideal.Quotient.mk _ (MvPolynomial.C r) :=
  RingHom.congr_fun (monicPowerFamilyCoverMap_comp p σ _
    (deltaDivisionFirstPowerCoefficients D d a u)
    (deltaDivisionFirstBaseToPolynomialQuotient D d a u)
    (fun s => Ideal.Quotient.mk _ (MvPolynomial.X s))
    (deltaDivisionFirstPolynomialQuotient_root_pow D d a u)) (Ideal.Quotient.mk _ r)

/-- 逆向き比較射は指定根を初期変数の剰余へ送る。 -/
@[simp] theorem deltaDivisionFirstPowerCoverToPolynomial_root
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) (s : σ) :
    deltaDivisionFirstPowerCoverToPolynomial D d a u
      (monicPowerFamilyRoot p σ _ (deltaDivisionFirstPowerCoefficients D d a u) s) =
      Ideal.Quotient.mk _ (MvPolynomial.X s) := monicPowerFamilyCoverMap_root ..

/-- 初期多項式商上では比較射の往復が恒等射。 -/
theorem deltaDivisionFirstPowerCoverToPolynomial_comp_forward
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) :
    (deltaDivisionFirstPowerCoverToPolynomial D d a u).comp
      (deltaDivisionFirstPolynomialToPowerCover D d a u) = RingHom.id _ := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro r
    change deltaDivisionFirstPowerCoverToPolynomial D d a u
      (deltaDivisionFirstPolynomialToPowerCover D d a u
        (Ideal.Quotient.mk _ (MvPolynomial.C r))) = _
    rw [deltaDivisionFirstPolynomialToPowerCover_coeff,
      deltaDivisionFirstPowerCoverToPolynomial_coeff]
    rfl
  · intro s
    change deltaDivisionFirstPowerCoverToPolynomial D d a u
      (deltaDivisionFirstPolynomialToPowerCover D d a u
        (Ideal.Quotient.mk _ (MvPolynomial.X s))) = _
    rw [deltaDivisionFirstPolynomialToPowerCover_root,
      deltaDivisionFirstPowerCoverToPolynomial_root]
    rfl

/-- 通常根添加環上でも比較射の往復が恒等射。 -/
theorem deltaDivisionFirstPolynomialToPowerCover_comp_backward
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) :
    (deltaDivisionFirstPolynomialToPowerCover D d a u).comp
      (deltaDivisionFirstPowerCoverToPolynomial D d a u) = RingHom.id _ := by
  apply RingHom.ext
  intro y
  obtain ⟨x, rfl⟩ := deltaDivisionFirstPolynomialToPowerCover_surjective D d a u y
  exact congrArg (deltaDivisionFirstPolynomialToPowerCover D d a u)
    (RingHom.congr_fun (deltaDivisionFirstPowerCoverToPolynomial_comp_forward D d a u) x)

/-- 初期係数多項式商は、A/(p,d,a_s)上の通常根添加環と同型。 -/
def deltaDivisionFirstCoefficientPowerEquiv
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) :
    (MvPolynomial σ A ⧸ deltaDivisionFirstPolynomialIdeal D d a u) ≃+*
      DeltaDivisionFirstPowerCover D d a u :=
  RingEquiv.ofRingHom (deltaDivisionFirstPolynomialToPowerCover D d a u)
    (deltaDivisionFirstPowerCoverToPolynomial D d a u)
    (deltaDivisionFirstPolynomialToPowerCover_comp_backward D d a u)
    (deltaDivisionFirstPowerCoverToPolynomial_comp_forward D d a u)

/-- 初期係数商の同型は元の係数の標準像を保つ。 -/
@[simp] theorem deltaDivisionFirstCoefficientPowerEquiv_coeff
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) (r : A) :
    deltaDivisionFirstCoefficientPowerEquiv D d a u (Ideal.Quotient.mk _ (MvPolynomial.C r)) =
      algebraMap (A ⧸ deltaDivisionFirstBaseIdeal (p := p) d a)
        (DeltaDivisionFirstPowerCover D d a u) (Ideal.Quotient.mk _ r) :=
  deltaDivisionFirstPolynomialToPowerCover_coeff D d a u r

/-- 初期係数商の同型は初期変数を指定根へ送る。 -/
@[simp] theorem deltaDivisionFirstCoefficientPowerEquiv_root
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) (s : σ) :
    deltaDivisionFirstCoefficientPowerEquiv D d a u (Ideal.Quotient.mk _ (MvPolynomial.X s)) =
      monicPowerFamilyRoot p σ _ (deltaDivisionFirstPowerCoefficients D d a u) s :=
  deltaDivisionFirstPolynomialToPowerCover_root D d a u s

/-- 実際の初期δ剰余は、適切な基底商上の通常根添加環の後続多項式環。 -/
def deltaDivisionFirstResiduePowerPolynomialEquiv
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) (hu : (u : A) = D.delta d) :
    (RelativeFreeDeltaRing (R := A) σ ⧸ deltaDivisionFirstResidueIdeal D d a) ≃+*
      MvPolynomial (σ × ℕ) (DeltaDivisionFirstPowerCover D d a u) :=
  (deltaDivisionFirstResiduePolynomialEquiv D d a u hu).trans
    (MvPolynomial.mapEquiv (σ × ℕ) (deltaDivisionFirstCoefficientPowerEquiv D d a u))

/-- 初期δ剰余の指定根は、通常根添加環の指定根の係数像。 -/
@[simp] theorem deltaDivisionFirstResiduePowerPolynomialEquiv_initial
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) (hu : (u : A) = D.delta d)
    (s : σ) :
    deltaDivisionFirstResiduePowerPolynomialEquiv D d a u hu
      (Ideal.Quotient.mk (deltaDivisionFirstResidueIdeal D d a) (MvPolynomial.X (s, 0))) =
      MvPolynomial.C
        (monicPowerFamilyRoot p σ _ (deltaDivisionFirstPowerCoefficients D d a u) s) := by
  change MvPolynomial.mapEquiv _ _
    (deltaDivisionFirstResiduePolynomialEquiv D d a u hu _) = _
  rw [deltaDivisionFirstResiduePolynomialEquiv_initial, MvPolynomial.mapEquiv_apply,
    MvPolynomial.map_C]
  exact congrArg MvPolynomial.C (deltaDivisionFirstCoefficientPowerEquiv_root D d a u s)

/-- 初期δ剰余の後続変数は通常根添加環上の自由変数。 -/
@[simp] theorem deltaDivisionFirstResiduePowerPolynomialEquiv_successor
    (D : DeltaStructure p A) (d : A) (a : σ → A) (u : Aˣ) (hu : (u : A) = D.delta d)
    (s : σ) (n : ℕ) :
    deltaDivisionFirstResiduePowerPolynomialEquiv D d a u hu
      (Ideal.Quotient.mk (deltaDivisionFirstResidueIdeal D d a) (MvPolynomial.X (s, n + 1))) =
      MvPolynomial.X (s, n) := by
  change MvPolynomial.mapEquiv _ _
    (deltaDivisionFirstResiduePolynomialEquiv D d a u hu _) = _
  rw [deltaDivisionFirstResiduePolynomialEquiv_successor, MvPolynomial.mapEquiv_apply,
    MvPolynomial.map_X]

end SerrePositivity.BhattScholze
