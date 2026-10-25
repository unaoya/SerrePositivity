module

public import SerrePositivity.BhattScholze.Semiperfectoid.RootedExtension.MonicPowerFamilyUniversal
public import Mathlib.RingTheory.Ideal.Quotient.Defs

/-! # 通常冪根添加環の商表示

通常のテンソル積による構成を、実際のモニック関係式による商へ結び付ける。
完備化やperfectoid性の比較はここでは主張しない。
-/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable (n : ℕ) (σ : Type u) (R : Type v) [CommRing R]

/-- 指定した冪根の関係式のイデアル。 -/
def monicPowerFamilyRelationIdeal (c : σ → R) : Ideal (MvPolynomial σ R) :=
  Ideal.span (Set.range fun s => MvPolynomial.X s ^ n - MvPolynomial.C (c s))

/-- 係数と指定根による多項式の評価。 -/
def monicPowerFamilyEvaluation (c : σ → R) :
    MvPolynomial σ R →+* MonicPowerFamilyCover n σ R c :=
  (MvPolynomial.aeval (monicPowerFamilyRoot n σ R c)).toRingHom

/-- 評価は実際の関係式イデアルを消す。 -/
theorem monicPowerFamilyEvaluation_kills (c : σ → R) :
    ∀ a ∈ monicPowerFamilyRelationIdeal n σ R c,
      monicPowerFamilyEvaluation n σ R c a = 0 := by
  have h : monicPowerFamilyRelationIdeal n σ R c ≤
      RingHom.ker (monicPowerFamilyEvaluation n σ R c) := by
    apply Ideal.span_le.mpr
    rintro _ ⟨s, rfl⟩
    change monicPowerFamilyEvaluation n σ R c
      (MvPolynomial.X s ^ n - MvPolynomial.C (c s)) = 0
    simp [monicPowerFamilyEvaluation, monicPowerFamilyRoot_pow]
  exact fun a ha => h ha

/-- 関係式の商から通常根添加環への具体的な写像。 -/
def monicPowerFamilyQuotientMap (c : σ → R) :
    MvPolynomial σ R ⧸ monicPowerFamilyRelationIdeal n σ R c →+*
      MonicPowerFamilyCover n σ R c :=
  Ideal.Quotient.lift _ (monicPowerFamilyEvaluation n σ R c)
    (monicPowerFamilyEvaluation_kills n σ R c)

/-- 商の標準変数は指定した冪根の関係式を満たす。 -/
theorem monicPowerFamilyQuotient_root_pow (c : σ → R) (s : σ) :
    (Ideal.Quotient.mk (monicPowerFamilyRelationIdeal n σ R c) (MvPolynomial.X s)) ^ n =
      algebraMap R (MvPolynomial σ R ⧸ monicPowerFamilyRelationIdeal n σ R c) (c s) := by
  have h := Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.subset_span (Set.mem_range_self s) :
      MvPolynomial.X s ^ n - MvPolynomial.C (c s) ∈
        monicPowerFamilyRelationIdeal n σ R c)
  rw [map_sub, map_pow, sub_eq_zero] at h
  exact h

/-- 指定根の普遍射による逆向きの写像。 -/
def monicPowerFamilyCoverToQuotient (c : σ → R) :
    MonicPowerFamilyCover n σ R c →+*
      MvPolynomial σ R ⧸ monicPowerFamilyRelationIdeal n σ R c :=
  monicPowerFamilyCoverMap n σ R c (algebraMap R _)
    (fun s => Ideal.Quotient.mk _ (MvPolynomial.X s))
    (monicPowerFamilyQuotient_root_pow n σ R c)

/-- 商からの写像と普遍射の合成は、根添加環上の恒等射。 -/
theorem monicPowerFamilyQuotientMap_comp_coverToQuotient (c : σ → R) :
    (monicPowerFamilyQuotientMap n σ R c).comp
      (monicPowerFamilyCoverToQuotient n σ R c) = RingHom.id _ := by
  apply monicPowerFamilyCoverHom_ext
  · ext r
    have h := RingHom.congr_fun (monicPowerFamilyCoverMap_comp n σ R c
      (algebraMap R _) (fun s => Ideal.Quotient.mk _ (MvPolynomial.X s))
      (monicPowerFamilyQuotient_root_pow n σ R c)) r
    change monicPowerFamilyQuotientMap n σ R c
      (monicPowerFamilyCoverToQuotient n σ R c (algebraMap R _ r)) = _
    rw [show monicPowerFamilyCoverToQuotient n σ R c (algebraMap R _ r) =
      algebraMap R _ r from h]
    change monicPowerFamilyEvaluation n σ R c (MvPolynomial.C r) = _
    simp [monicPowerFamilyEvaluation]
  · intro s
    change monicPowerFamilyQuotientMap n σ R c
      (monicPowerFamilyCoverToQuotient n σ R c (monicPowerFamilyRoot n σ R c s)) = _
    rw [show monicPowerFamilyCoverToQuotient n σ R c (monicPowerFamilyRoot n σ R c s) =
      Ideal.Quotient.mk _ (MvPolynomial.X s) from monicPowerFamilyCoverMap_root ..]
    change monicPowerFamilyEvaluation n σ R c (MvPolynomial.X s) = _
    simp [monicPowerFamilyEvaluation]

/-- 逆の合成も実際の関係式商上の恒等射。 -/
theorem monicPowerFamilyCoverToQuotient_comp_quotientMap (c : σ → R) :
    (monicPowerFamilyCoverToQuotient n σ R c).comp
      (monicPowerFamilyQuotientMap n σ R c) = RingHom.id _ := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro r
    change monicPowerFamilyCoverToQuotient n σ R c
      (monicPowerFamilyEvaluation n σ R c (MvPolynomial.C r)) = _
    rw [show monicPowerFamilyEvaluation n σ R c (MvPolynomial.C r) =
      algebraMap R _ r by simp [monicPowerFamilyEvaluation]]
    exact RingHom.congr_fun (monicPowerFamilyCoverMap_comp n σ R c
      (algebraMap R _) (fun s => Ideal.Quotient.mk _ (MvPolynomial.X s))
      (monicPowerFamilyQuotient_root_pow n σ R c)) r
  · intro s
    change monicPowerFamilyCoverToQuotient n σ R c
      (monicPowerFamilyEvaluation n σ R c (MvPolynomial.X s)) = _
    rw [show monicPowerFamilyEvaluation n σ R c (MvPolynomial.X s) =
      monicPowerFamilyRoot n σ R c s by simp [monicPowerFamilyEvaluation]]
    exact monicPowerFamilyCoverMap_root ..

/-- 通常冪根添加環は、モニック関係式による商と同型。 -/
def monicPowerFamilyPresentationEquiv (c : σ → R) :
    MvPolynomial σ R ⧸ monicPowerFamilyRelationIdeal n σ R c ≃+*
      MonicPowerFamilyCover n σ R c :=
  RingEquiv.ofRingHom (monicPowerFamilyQuotientMap n σ R c)
    (monicPowerFamilyCoverToQuotient n σ R c)
    (monicPowerFamilyQuotientMap_comp_coverToQuotient n σ R c)
    (monicPowerFamilyCoverToQuotient_comp_quotientMap n σ R c)

/-- 商表示同型は標準係数射と両立する。 -/
@[simp] theorem monicPowerFamilyPresentationEquiv_coeff (c : σ → R) (r : R) :
    monicPowerFamilyPresentationEquiv n σ R c (algebraMap R _ r) =
      algebraMap R (MonicPowerFamilyCover n σ R c) r := by
  change monicPowerFamilyEvaluation n σ R c (MvPolynomial.C r) = _
  simp [monicPowerFamilyEvaluation]

/-- 商表示同型は変数の剰余を指定した根へ送る。 -/
@[simp] theorem monicPowerFamilyPresentationEquiv_root (c : σ → R) (s : σ) :
    monicPowerFamilyPresentationEquiv n σ R c
      (Ideal.Quotient.mk _ (MvPolynomial.X s)) = monicPowerFamilyRoot n σ R c s := by
  change monicPowerFamilyEvaluation n σ R c (MvPolynomial.X s) = _
  simp [monicPowerFamilyEvaluation]

/-- 標準R代数構造についてのモニック商表示同型。 -/
def monicPowerFamilyPresentationAlgEquiv (c : σ → R) :
    (MvPolynomial σ R ⧸ monicPowerFamilyRelationIdeal n σ R c) ≃ₐ[R]
      MonicPowerFamilyCover n σ R c :=
  AlgEquiv.ofRingEquiv (monicPowerFamilyPresentationEquiv_coeff n σ R c)

end SerrePositivity.BhattScholze
