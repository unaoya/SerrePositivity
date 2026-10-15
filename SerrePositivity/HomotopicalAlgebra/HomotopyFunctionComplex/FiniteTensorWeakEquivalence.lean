module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FiniteTensorSkeleton
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.TensorPushout

/-! # Weak equivalences under a homotopically constant finite tensor -/

@[expose] public section
universe v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Reedy

namespace SerrePositivity.HomotopyFunctionComplex.FiniteTensor
variable {C : Type u} [Category.{v} C] [ModelCategory C] (A : SimplexCategory ⥤ C)
  (hconst : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (A.map f))

include hconst in
lemma standard_map_weakEquivalence {n m : SimplexCategory} (f : n ⟶ m) :
    weakEquivalences C (map A (SSet.stdSimplex.{v}.map f)) := by
  have h := (weakEquivalences C).comp_mem _ _
    ((weakEquivalences C).of_isIso
      (representationIso A (SSet.stdSimplex.obj n) (Iso.refl _)).hom) (hconst f)
  have hn := standard_naturality A f
  have hm : weakEquivalences C
      (map A (SSet.stdSimplex.{v}.map f) ≫
        (representationIso A (SSet.stdSimplex.obj m) (Iso.refl _)).hom) := hn.symm ▸ h
  exact (weakEquivalences C).of_postcomp _ _
    ((weakEquivalences C).of_isIso
      (representationIso A (SSet.stdSimplex.obj m) (Iso.refl _)).hom) hm

include hconst in
lemma map_between_representables {X Y : SSet.{v}}
    [X.Nonsingular] [X.Finite] [Y.Nonsingular] [Y.Finite]
    {n m : SimplexCategory} (eX : SSet.stdSimplex.obj n ≅ X)
    (eY : SSet.stdSimplex.obj m ≅ Y) (f : X ⟶ Y) :
    weakEquivalences C (map A f) := by
  let g := eX.hom ≫ f ≫ eY.inv
  have hg : weakEquivalences C (map A g) := by
    obtain ⟨k, hk⟩ := SSet.stdSimplex.map_surjective g
    exact hk ▸ standard_map_weakEquivalence A hconst k
  have : IsIso (map A eX.hom) := inferInstanceAs (IsIso (iso A eX).hom)
  have : IsIso (map A eY.inv) := inferInstanceAs (IsIso (iso A eY.symm).hom)
  have he : map A g = map A eX.hom ≫ (map A f ≫ map A eY.inv) :=
    ((map_comp A eX.hom (f ≫ eY.inv)).symm).trans
      (congrArg (fun k ↦ map A eX.hom ≫ k) (map_comp A f eY.inv).symm)
  exact (weakEquivalences C).of_postcomp _ _ ((weakEquivalences C).of_isIso _)
    ((weakEquivalences C).of_precomp _ _ ((weakEquivalences C).of_isIso _) (he ▸ hg))

/-- A proposition recording a standard simplex presentation, with no choice
of its dimension included in the tensor construction. -/
def IsStandardSimplex (X : SSet.{v}) : Prop :=
  ∃ n : SimplexCategory, Nonempty (SSet.stdSimplex.obj n ≅ X)

include hconst in
lemma map_weakEquivalence_of_isStandardSimplex {X Y : SSet.{v}}
    [X.Nonsingular] [X.Finite] [Y.Nonsingular] [Y.Finite]
    (hX : IsStandardSimplex X) (hY : IsStandardSimplex Y) (f : X ⟶ Y) :
    weakEquivalences C (map A f) := by
  obtain ⟨n, ⟨eX⟩⟩ := hX
  obtain ⟨m, ⟨eY⟩⟩ := hY
  exact map_between_representables A hconst eX eY f

include hconst in
/-- A finite nonempty cover whose every intersection is a standard simplex
has weakly equivalent tensor to its ambient standard simplex. The ambient
subcomplex is included among the intersections (the empty index set). -/
lemma map_finite_cover_weakEquivalence
    (hA : reedyLeft simplex (cofibrations C) (initial.to A))
    {n : SimplexCategory} {ι : Type*}
    (U : ι → (SSet.stdSimplex.{v}.obj n).Subcomplex) (s : Finset ι)
    (B : (SSet.stdSimplex.{v}.obj n).Subcomplex) (hs : s.Nonempty)
    (hrep : ∀ t : Finset ι, t ⊆ s → IsStandardSimplex (B ⊓ t.inf U).toSSet) :
    weakEquivalences C (map A (SSet.Subcomplex.homOfLE
      (inf_le_left : B ⊓ s.sup U ≤ B))) := by
  classical
  induction s using Finset.induction_on generalizing B with
  | empty => exact (Finset.not_nonempty_empty hs).elim
  | @insert a s ha ih =>
    by_cases hs' : s.Nonempty
    · have hold := ih B hs' (fun t ht ↦ hrep t (ht.trans (Finset.subset_insert _ _)))
      have hinter := ih (B ⊓ U a) hs' (fun t ht ↦ by
        have h := hrep (insert a t) (Finset.insert_subset_insert a ht)
        simpa only [Finset.inf_insert, inf_assoc] using h)
      let P := B ⊓ s.sup U
      let Q := B ⊓ U a
      let L := Q ⊓ s.sup U
      let R := B ⊓ (insert a s).sup U
      have sq : SSet.Subcomplex.BicartSq L P Q R :=
        { sup_eq := by
            dsimp [P, Q, R]
            rw [Finset.sup_insert]
            ext m x
            change ((x ∈ B.obj m ∧ x ∈ (s.sup U).obj m) ∨
              (x ∈ B.obj m ∧ x ∈ (U a).obj m)) ↔
                (x ∈ B.obj m ∧ (x ∈ (U a).obj m ∨ x ∈ (s.sup U).obj m))
            tauto
          inf_eq := by
            dsimp [L, P, Q]
            ext m x
            change ((x ∈ B.obj m ∧ x ∈ (s.sup U).obj m) ∧
              (x ∈ B.obj m ∧ x ∈ (U a).obj m)) ↔
                ((x ∈ B.obj m ∧ x ∈ (U a).obj m) ∧ x ∈ (s.sup U).obj m)
            tauto }
      have ht : trivialCofibrations C (map A (SSet.Subcomplex.homOfLE sq.le₁₃)) :=
        ⟨map_mono_cofibration A hA _, hinter⟩
      have hp : trivialCofibrations C (map A (SSet.Subcomplex.homOfLE sq.le₂₄)) :=
        (trivialCofibrations C).of_isPushout (FiniteTensor.isPushout A sq.isPushout) ht
      exact (weakEquivalences C).of_precomp _ _ hp.2
        ((map_comp A (SSet.Subcomplex.homOfLE sq.le₂₄)
          (SSet.Subcomplex.homOfLE (inf_le_left : R ≤ B))).symm ▸ hold)
    · have hse : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs'
      subst s
      apply map_weakEquivalence_of_isStandardSimplex A hconst
      · simpa using hrep {a} (by simp)
      · simpa using hrep ∅ (by simp)

end SerrePositivity.HomotopyFunctionComplex.FiniteTensor
