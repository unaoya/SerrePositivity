module

public import SerrePositivity.BhattScholze.Semiperfectoid.RootedExtension.CompatibleRoot.CompatibleRootFamilyQuotient

/-! # 一元添字の根族と既存の単一根商・完備化の比較

元の単一根の台環と標準射を変更せず、イデアルの一致から比較する。
根の関係式、素数性、完備性、perfectoid性はこの比較自体には要求しない。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {R : Type u} [CommRing R]

/-- 一元添字族の初期イデアルは、元の単一根の初期主イデアル。 -/
theorem compatibleRootFamilyZeroIdeal_singleton (ρ : ℕ → R) :
    compatibleRootFamilyZeroIdeal (fun _ : PUnit.{u+1} ↦ ρ) = Ideal.span {ρ 0} := by
  change Ideal.span (Set.range (fun _ : PUnit.{u+1} ↦ ρ 0)) = Ideal.span {ρ 0}
  rw [Set.range_const]

/-- 一元添字族の全根イデアルは、元の単一根イデアル。 -/
theorem compatibleRootFamilyIdeal_singleton (ρ : ℕ → R) :
    compatibleRootFamilyIdeal (fun _ : PUnit.{u+1} ↦ ρ) = compatibleRootIdeal ρ := by
  change Ideal.span (Set.range (fun x : PUnit.{u+1} × ℕ ↦ ρ x.2)) =
    Ideal.span (Set.range ρ)
  congr 1
  ext x
  constructor
  · rintro ⟨⟨_, n⟩, rfl⟩
    exact ⟨n, rfl⟩
  · rintro ⟨n, rfl⟩
    exact ⟨(PUnit.unit, n), rfl⟩

/-- 初期イデアルの一致による標準商比較。 -/
def compatibleRootSingletonZeroQuotientEquiv (ρ : ℕ → R) :
    R ⧸ compatibleRootFamilyZeroIdeal (fun _ : PUnit.{u+1} ↦ ρ) ≃+* R ⧸ Ideal.span {ρ 0} :=
  Ideal.quotEquivOfEq (compatibleRootFamilyZeroIdeal_singleton ρ)

@[simp] theorem compatibleRootSingletonZeroQuotientEquiv_mk (ρ : ℕ → R) (r : R) :
    compatibleRootSingletonZeroQuotientEquiv ρ (Ideal.Quotient.mk _ r) =
      Ideal.Quotient.mk _ r := rfl

/-- 全根イデアルの一致による標準商比較。 -/
def compatibleRootSingletonQuotientEquiv (ρ : ℕ → R) :
    R ⧸ compatibleRootFamilyIdeal (fun _ : PUnit.{u+1} ↦ ρ) ≃+* R ⧸ compatibleRootIdeal ρ :=
  Ideal.quotEquivOfEq (compatibleRootFamilyIdeal_singleton ρ)

@[simp] theorem compatibleRootSingletonQuotientEquiv_mk (ρ : ℕ → R) (r : R) :
    compatibleRootSingletonQuotientEquiv ρ (Ideal.Quotient.mk _ r) =
      Ideal.Quotient.mk _ r := rfl

/-- 二つの商比較は、初期商から全根商への元の標準射と可換。 -/
theorem compatibleRootSingletonQuotientEquiv_comp_quotientMap (ρ : ℕ → R) :
    (compatibleRootSingletonQuotientEquiv ρ).toRingHom.comp
        (compatibleRootFamilyQuotientMap (fun _ : PUnit.{u+1} ↦ ρ)) =
      (compatibleRootQuotientMap ρ).comp
        (compatibleRootSingletonZeroQuotientEquiv ρ).toRingHom := by
  apply Ideal.Quotient.ringHom_ext
  rfl

/-- 同じ全根イデアルの一致だけを使った、既存p完備化の比較。 -/
def compatibleRootSingletonCompletionEquiv (p : ℕ) (ρ : ℕ → R) :
    CompatibleRootFamilyCompletion p (fun _ : PUnit.{u+1} ↦ ρ) ≃+* CompatibleRootCompletion p ρ :=
  RingEquiv.cast (R := fun I : Ideal R ↦ AdicCompletion (Ideal.span {(p : R ⧸ I)}) (R ⧸ I))
    (compatibleRootFamilyIdeal_singleton ρ)

private theorem completionCast_algebraMap (p : ℕ) {I J : Ideal R} (h : I = J) (x : R ⧸ I) :
    RingEquiv.cast (R := fun K : Ideal R ↦ AdicCompletion (Ideal.span {(p : R ⧸ K)}) (R ⧸ K)) h
        (algebraMap (R ⧸ I) _ x) =
      algebraMap (R ⧸ J) _ (Ideal.quotEquivOfEq h x) := by
  subst J
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

/-- 完備化比較は、全根商からの元の標準単位を保つ。 -/
@[simp] theorem compatibleRootSingletonCompletionEquiv_algebraMap (p : ℕ) (ρ : ℕ → R)
    (x : R ⧸ compatibleRootFamilyIdeal (fun _ : PUnit.{u+1} ↦ ρ)) :
    compatibleRootSingletonCompletionEquiv p ρ (algebraMap _ _ x) =
      algebraMap _ (CompatibleRootCompletion p ρ) (compatibleRootSingletonQuotientEquiv ρ x) :=
  completionCast_algebraMap p (compatibleRootFamilyIdeal_singleton ρ) x

/-- 完備化比較は、初期商からの既存compatibleRootCompletionMapを保つ。 -/
theorem compatibleRootSingletonCompletionEquiv_comp_completionMap (p : ℕ) (ρ : ℕ → R) :
    (compatibleRootSingletonCompletionEquiv p ρ).toRingHom.comp
        (compatibleRootFamilyCompletionMap p (fun _ : PUnit.{u+1} ↦ ρ)) =
      (compatibleRootCompletionMap p ρ).comp
        (compatibleRootSingletonZeroQuotientEquiv ρ).toRingHom := by
  apply Ideal.Quotient.ringHom_ext
  apply RingHom.ext
  intro r
  change compatibleRootSingletonCompletionEquiv p ρ
      (algebraMap (R ⧸ compatibleRootFamilyIdeal (fun _ : PUnit.{u+1} ↦ ρ)) _
        (Ideal.Quotient.mk (compatibleRootFamilyIdeal (fun _ : PUnit.{u+1} ↦ ρ)) r)) =
    compatibleRootCompletionMap p ρ
      (compatibleRootSingletonZeroQuotientEquiv ρ
        (Ideal.Quotient.mk (compatibleRootFamilyZeroIdeal (fun _ : PUnit.{u+1} ↦ ρ)) r))
  rw [compatibleRootSingletonCompletionEquiv_algebraMap,
    compatibleRootSingletonQuotientEquiv_mk, compatibleRootSingletonZeroQuotientEquiv_mk]
  rfl

end SerrePositivity.BhattScholze
