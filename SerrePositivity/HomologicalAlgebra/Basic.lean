module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.Linear
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.Linear
public import Mathlib.Algebra.Homology.Single

/-!
# 複体についての基本補題

- 項が零ならホモロジーも零（`isZero_homology_of_isZero_X`）、各項が零なら複体も零。
- 自由加群は圏論的に射影的。
- `smulId a K = a • 𝟙 K`。`homologyMap`・`single` はスカラー倍と両立する（任意の複体の形）。
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace SerrePositivity

/-- 項が零ならホモロジーも零（任意のアーベル圏）。 -/
lemma isZero_homology_of_isZero_X {C : Type*} [Category* C] [Abelian C] {ι : Type*}
    {c : ComplexShape ι} (K : HomologicalComplex C c) (i : ι) (h : IsZero (K.X i)) :
    IsZero (K.homology i) :=
  (HomologicalComplex.exactAt_iff_isZero_homology _ _).mp (ShortComplex.exact_of_isZero_X₂ _ h)

variable {R : Type u} [CommRing R]

/-- 各項が零な複体は零。 -/
lemma isZero_of_isZero_X {P : CochainComplex (ModuleCat.{u} R) ℤ} (h : ∀ i, IsZero (P.X i)) :
    IsZero P := by
  rw [IsZero.iff_id_eq_zero]
  exact HomologicalComplex.hom_ext _ _ fun i ↦ (h i).eq_of_src _ _

/-- 自由加群は圏論的に射影的。 -/
lemma projective_of_free {M : ModuleCat.{u} R} (h : Module.Free R M) : Projective M := by
  have : Module.Projective R M := Module.Projective.of_free
  exact M.projective_of_categoryTheory_projective

/-- 複体 `K` の自己射 `a • 𝟙 K`。 -/
noncomputable def smulId (a : R) (K : CochainComplex (ModuleCat.{u} R) ℤ) : K ⟶ K :=
  a • 𝟙 K

section shape

variable {ι : Type*} {c : ComplexShape ι}

/-- `homologyMap` はスカラー倍と両立する（任意の複体の形）。 -/
lemma homologyMap_smul {K L : HomologicalComplex (ModuleCat.{u} R) c} (f : K ⟶ L) (a : R)
    (i : ι) :
    HomologicalComplex.homologyMap (a • f) i = a • HomologicalComplex.homologyMap f i := by
  have : (HomologicalComplex.shortComplexFunctor _ _ i).map (a • f) =
      a • (HomologicalComplex.shortComplexFunctor _ _ i).map f := by
    ext <;> rfl
  simp only [HomologicalComplex.homologyMap, this, ShortComplex.homologyMap_smul]
  rfl

/-- `single` はスカラー倍と両立する。 -/
lemma single_map_smul [DecidableEq ι] (j : ι) {X Y : ModuleCat.{u} R} (r : R) (f : X ⟶ Y) :
    (HomologicalComplex.single (ModuleCat.{u} R) c j).map (r • f) =
      r • (HomologicalComplex.single (ModuleCat.{u} R) c j).map f := by
  apply HomologicalComplex.hom_ext
  intro i
  by_cases h : i = j
  · subst h
    simp [HomologicalComplex.single_map_f_self]
  · exact (HomologicalComplex.isZero_single_obj_X c j X i h).eq_of_src _ _

end shape

end SerrePositivity
