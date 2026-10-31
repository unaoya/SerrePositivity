module

public import SerrePositivity.Asymptotic.SequenceSupport
public import SerrePositivity.CategoryTheory.HomotopyProperty
public import SerrePositivity.CommutativeAlgebra.Koszul

/-! # 自由複体列に対する具体的な Koszul 構成 -/

@[expose] public section

universe u

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

variable {R : Type u} [CommRing R] {s : ℕ → ℕ}

/-- 自由列の圏でスカラー作用の錐を反復する。 -/
noncomputable def sequenceKoszul : {n : ℕ} → (Fin n → R) →
    CochainComplex (FreeSequence R s) ℤ → CochainComplex (FreeSequence R s) ℤ
  | 0, _, K => K
  | n + 1, x, K =>
      CochainComplex.mappingCone (x (Fin.last n) • 𝟙 (sequenceKoszul (Fin.init x) K))

lemma sequenceKoszul_bounded {n : ℕ} (x : Fin n → R)
    (K : CochainComplex (FreeSequence R s) ℤ) (hK : strictlyBoundedComplex _ K) :
    strictlyBoundedComplex _ (sequenceKoszul x K) := by
  induction n with
  | zero => exact hK
  | succ n ih => exact strictlyBoundedComplex_mappingCone _ _ (ih _) (ih _)

/-- 各段への評価は既存の係数つき Koszul 複体と一致する。 -/
noncomputable def evaluateSequenceKoszulIso : ∀ {m : ℕ} (x : Fin m → R)
    (K : CochainComplex (FreeSequence R s) ℤ) (n : ℕ),
    (evaluateComplex n).obj (sequenceKoszul x K) ≅
      koszulComplexOn x ((evaluateComplex n).obj K)
  | 0, _, _, _ => Iso.refl _
  | m + 1, x, K, n => by
      let a := x (Fin.last m)
      let P := sequenceKoszul (Fin.init x) K
      have : (evaluateComplex (R := R) (s := s) n).Linear R :=
        inferInstanceAs (((FreeSequence.evaluation n).mapHomologicalComplex (.up ℤ)).Linear R)
      let e := CochainComplex.mappingCone.mapHomologicalComplexIso (a • 𝟙 P)
        (FreeSequence.evaluation n)
      have h : (evaluateComplex n).map (a • 𝟙 P) = smulId a ((evaluateComplex n).obj P) := by
        rw [Functor.map_smul, (evaluateComplex n).map_id]
        rfl
      let e' := eqToIso (congrArg
        (fun f : (evaluateComplex n).obj P ⟶ (evaluateComplex n).obj P ↦
          CochainComplex.mappingCone f) h)
      exact e ≪≫ e' ≪≫
        (scalarConeFunctor a).mapIso (evaluateSequenceKoszulIso (Fin.init x) K n)

/-- 有界自由列の射の具体的な写像錐三角形。 -/
@[implicit_reducible]
noncomputable def sequenceConeTriangle {K L : CochainComplex (FreeSequence R s) ℤ}
    (f : K ⟶ L) (hK : strictlyBoundedComplex _ K) (hL : strictlyBoundedComplex _ L) :
    Triangle (SequenceHomotopy R s) :=
  fullSubcategoryTriangle (boundedHomotopyProperty (FreeSequence R s))
    (CochainComplex.mappingCone.triangleh f)
    ((boundedHomotopyProperty_quotient _ K).mpr hK)
    ((boundedHomotopyProperty_quotient _ L).mpr hL)
    ((boundedHomotopyProperty_quotient _ _).mpr (strictlyBoundedComplex_mappingCone _ f hK hL))

lemma sequenceConeTriangle_distinguished {K L : CochainComplex (FreeSequence R s) ℤ}
    (f : K ⟶ L) (hK : strictlyBoundedComplex _ K) (hL : strictlyBoundedComplex _ L) :
    sequenceConeTriangle f hK hL ∈ distTriang (SequenceHomotopy R s) :=
  fullSubcategoryTriangle_distinguished _ _ _ _ _
    (HomotopyCategory.mappingCone_triangleh_distinguished f)

@[simp] lemma sequenceConeTriangle_smul_mor₁
    (a : R) (K : CochainComplex (FreeSequence R s) ℤ) (hK : strictlyBoundedComplex _ K) :
    (sequenceConeTriangle (a • 𝟙 K) hK hK).mor₁ = a • 𝟙 (sequenceHomotopyObj K hK) := by
  apply ObjectProperty.hom_ext
  change (HomotopyCategory.quotient _ _).map (a • 𝟙 K) = a • 𝟙 _
  rw [Functor.map_smul, (HomotopyCategory.quotient _ _).map_id]
  rfl

end SerrePositivity.Asymptotic
