module

public import SerrePositivity.BhattScholze.Delta.Free.RelativeFreeFiniteVariableSplit

/-! # 相対自由δ計算の有限段表示

初期N+1段の多項式のδ像を初期N+2段で計算する。
同じ有限段にδ構造を与えることは要求しない。
-/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable (N : ℕ) (σ : Type v)

/-- 初期有限変数を次の有限段へ含める標準多項式射。 -/
def relativeFreeFiniteStepInclusion :
    MvPolynomial (σ × Fin (N + 1)) A →+* MvPolynomial (σ × Fin (N + 2)) A :=
  (MvPolynomial.rename fun z => (z.1, z.2.castSucc)).toRingHom

/-- 有限初期変数の標準包含は単射。零係数環も含む。 -/
theorem relativeFreeFiniteInitialPolynomialMap_injective :
    Function.Injective (relativeFreeFiniteInitialPolynomialMap N σ A) := by
  apply MvPolynomial.rename_injective
  intro x y h
  exact Prod.ext (congrArg (fun z : σ × ℕ => z.1) h)
    (Fin.ext (congrArg (fun z : σ × ℕ => z.2) h))

/-- 一段大きい有限多項式環へのW₂計算射。 -/
def relativeFreeFiniteDeltaStepSection (D : DeltaStructure p A) :
    MvPolynomial (σ × Fin (N + 1)) A →+* WittTwo p (MvPolynomial (σ × Fin (N + 2)) A) :=
  MvPolynomial.eval₂Hom ((wittTwoMap (p := p) MvPolynomial.C).comp D.sectionHom)
    (fun z => TruncatedWittVector.mk p (fun i => if i = 0 then
      MvPolynomial.X (z.1, z.2.castSucc) else MvPolynomial.X (z.1, z.2.succ)))

/-- W₂計算射の係数上の式。 -/
@[simp] theorem relativeFreeFiniteDeltaStepSection_C (D : DeltaStructure p A) (a : A) :
    relativeFreeFiniteDeltaStepSection N σ D (MvPolynomial.C a) =
      wittTwoMap (p := p) MvPolynomial.C (D.sectionHom a) := by
  exact MvPolynomial.eval₂Hom_C _ _ a

/-- W₂計算射の変数上の式。 -/
@[simp] theorem relativeFreeFiniteDeltaStepSection_X (D : DeltaStructure p A)
    (s : σ) (i : Fin (N + 1)) :
    relativeFreeFiniteDeltaStepSection N σ D (MvPolynomial.X (s, i)) =
      TruncatedWittVector.mk p (fun j => if j = 0 then
        MvPolynomial.X (s, i.castSucc) else MvPolynomial.X (s, i.succ)) := by
  exact MvPolynomial.eval₂Hom_X' _ _ (s, i)

/-- 第0座標は次の有限段への標準包含。 -/
theorem relativeFreeFiniteDeltaStepSection_projection (D : DeltaStructure p A) :
    (wittTwoProjection p (MvPolynomial (σ × Fin (N + 2)) A)).comp
      (relativeFreeFiniteDeltaStepSection N σ D) = relativeFreeFiniteStepInclusion N σ := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp only [RingHom.comp_apply, relativeFreeFiniteDeltaStepSection_C,
      wittTwoProjection_apply, wittTwoMap_coeff]
    rw [D.coeff_zero]
    simp [relativeFreeFiniteStepInclusion]
  · intro z
    obtain ⟨s, i⟩ := z
    simp [relativeFreeFiniteDeltaStepSection_X, relativeFreeFiniteStepInclusion]

/-- 第1座標として一段大きい有限環で計算したδ像。 -/
def relativeFreeFiniteDeltaStep (D : DeltaStructure p A)
    (f : MvPolynomial (σ × Fin (N + 1)) A) : MvPolynomial (σ × Fin (N + 2)) A :=
  (relativeFreeFiniteDeltaStepSection N σ D f).coeff 1

/-- 有限δ計算の係数上の式。 -/
@[simp] theorem relativeFreeFiniteDeltaStep_C (D : DeltaStructure p A) (a : A) :
    relativeFreeFiniteDeltaStep N σ D (MvPolynomial.C a) = MvPolynomial.C (D.delta a) := by
  simp only [relativeFreeFiniteDeltaStep, relativeFreeFiniteDeltaStepSection_C, wittTwoMap_coeff]
  rfl

/-- 有限δ計算の変数上の式。 -/
@[simp] theorem relativeFreeFiniteDeltaStep_X (D : DeltaStructure p A)
    (s : σ) (i : Fin (N + 1)) :
    relativeFreeFiniteDeltaStep N σ D (MvPolynomial.X (s, i)) = MvPolynomial.X (s, i.succ) := by
  simp [relativeFreeFiniteDeltaStep]

/-- 有限W₂計算と元の相対自由W₂切断の可換図式。 -/
theorem relativeFreeFiniteDeltaStepSection_naturality (D : DeltaStructure p A) :
    (wittTwoMap (p := p) (relativeFreeFiniteInitialPolynomialMap (N + 2) σ A).toRingHom).comp
      (relativeFreeFiniteDeltaStepSection N σ D) =
      (relativeFreeDeltaSection σ D).comp
        (relativeFreeFiniteInitialPolynomialMap (N + 1) σ A).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro a
    apply TruncatedWittVector.ext
    intro i
    simp [relativeFreeFiniteDeltaStepSection_C, relativeFreeFiniteInitialPolynomialMap,
      relativeFreeDeltaSection, wittTwoMap_coeff]
  · intro z
    obtain ⟨s, i⟩ := z
    apply TruncatedWittVector.ext
    intro j
    fin_cases j <;>
      simp [relativeFreeFiniteDeltaStepSection_X, relativeFreeFiniteInitialPolynomialMap,
        relativeFreeDeltaSection, wittTwoMap_coeff]

/-- 任意有限初期多項式の実際のδ像は、次の有限初期段の多項式で表せる。 -/
theorem relativeFreeFiniteDeltaStep_delta_image (D : DeltaStructure p A)
    (f : MvPolynomial (σ × Fin (N + 1)) A) :
    (relativeFreeDeltaStructure σ D).delta
      (relativeFreeFiniteInitialPolynomialMap (N + 1) σ A f) =
      relativeFreeFiniteInitialPolynomialMap (N + 2) σ A (relativeFreeFiniteDeltaStep N σ D f) := by
  have h := congrArg (fun z : WittTwo p (RelativeFreeDeltaRing (R := A) σ) => z.coeff 1)
    (RingHom.congr_fun (relativeFreeFiniteDeltaStepSection_naturality N σ D) f)
  simp only [RingHom.comp_apply, wittTwoMap_coeff] at h
  exact h.symm

end SerrePositivity.BhattScholze
