module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.AdicCompletion.Functoriality

/-! # 剰余加群の忠実平坦降下とadic全射判定 -/

@[expose] public noncomputable section
namespace SerrePositivity
variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]

/-- Iで割った加群。R/I作用にはMathlibの既存instanceを使う。 -/
abbrev AdicReduction (I : Ideal R) (M : Type*) [AddCommGroup M] [Module R M] :=
  M ⧸ I • (⊤ : Submodule R M)

/-- 線形写像が剰余加群の間に誘導するR/I線形写像。 -/
def adicReductionMap (I : Ideal R) (f : M →ₗ[R] N) :
    AdicReduction I M →ₗ[R ⧸ I] AdicReduction I N :=
  let q := (I • (⊤ : Submodule R M)).mapQ (I • (⊤ : Submodule R N)) f
    (Submodule.smul_top_le_comap_smul_top I f)
  { toFun := q
    map_add' := q.map_add
    map_smul' := by
      intro r x
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
      obtain ⟨x, rfl⟩ := (I • (⊤ : Submodule R M)).mkQ_surjective x
      exact congrArg (I • (⊤ : Submodule R N)).mkQ (f.map_smul r x) }

/-- 剰余写像は元の写像と標準商写像の図式を保つ。 -/
@[simp] theorem adicReductionMap_mkQ (I : Ideal R) (f : M →ₗ[R] N) (x : M) :
    adicReductionMap I f ((I • (⊤ : Submodule R M)).mkQ x) =
      (I • (⊤ : Submodule R N)).mkQ (f x) := rfl

/-- 標準商写像との合成としての可換図式。 -/
theorem adicReductionMap_comp_mkQ (I : Ideal R) (f : M →ₗ[R] N) :
    adicReductionMap I f ∘ (I • (⊤ : Submodule R M)).mkQ =
      (I • (⊤ : Submodule R N)).mkQ ∘ f := rfl

/-- 剰余写像が忠実平坦な加群による底変換後に全射なら、元の写像は全射。
始域の前完備性と終域の分離性だけを要し、Iの有限生成性は不要。 -/
theorem surjective_of_faithfullyFlat_adicReduction
    (I : Ideal R) [IsPrecomplete I M] [IsHausdorff I N]
    (E : Type*) [AddCommGroup E] [Module (R ⧸ I) E]
    [Module.FaithfullyFlat (R ⧸ I) E] (f : M →ₗ[R] N)
    (h : Function.Surjective ((adicReductionMap I f).lTensor E)) :
    Function.Surjective f := by
  have hb := (Module.FaithfullyFlat.lTensor_surjective_iff_surjective
    (R ⧸ I) E (adicReductionMap I f)).mp h
  apply surjective_of_mkQ_comp_surjective (I := I) (f := f)
  intro y
  obtain ⟨x, hx⟩ := hb y
  obtain ⟨x, rfl⟩ := (I • (⊤ : Submodule R M)).mkQ_surjective x
  exact ⟨x, hx⟩

end SerrePositivity
