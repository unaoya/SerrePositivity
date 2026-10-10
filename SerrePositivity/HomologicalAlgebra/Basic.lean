module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.Linear
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.Linear
public import Mathlib.Algebra.Homology.Single
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.Basis.Prod
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Finiteness.Prod
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# 複体についての基本補題

- 項が零ならホモロジーも零（`isZero_homology_of_isZero_X`）、各項が零なら複体も零。
- 自由加群は圏論的に射影的。
- `smulId a K = a • 𝟙 K`。`homologyMap`・`single` はスカラー倍と両立する（任意の複体の形）。

後半では零対象、有限直和、写像錐の項の自由性・有限生成性と、
Noether 環上のホモロジーの有限生成性を扱う。
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

end

/-!
## 複体の項の自由性・有限性

零加群・biproduct・写像錐の項が有限自由であること。
Noether 環上では、各項が有限生成な複体のホモロジーも有限生成（`homology_moduleFinite`）。
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace SerrePositivity

variable {R : Type u} [CommRing R]

/-- 加群圏の零対象は自由加群である。空の基底に対応する Mathlib のインスタンスを使う。 -/
lemma isZero_moduleCat_free {M : ModuleCat.{u} R} (h : IsZero M) : Module.Free R M := by
  have : Subsingleton M := ModuleCat.isZero_iff_subsingleton.mp h
  infer_instance

/-- 加群圏の零対象は有限生成である。零加群に対する Mathlib のインスタンスを使う。 -/
lemma isZero_moduleCat_finite {M : ModuleCat.{u} R} (h : IsZero M) : Module.Finite R M := by
  have : Subsingleton M := ModuleCat.isZero_iff_subsingleton.mp h
  infer_instance

/-- 二つの加群の biproduct は自由・有限を保つ。 -/
lemma free_finite_biprod (M N : ModuleCat.{u} R) [Module.Free R M] [Module.Free R N]
    [Module.Finite R M] [Module.Finite R N] :
    Module.Free R (M ⊞ N : ModuleCat.{u} R) ∧ Module.Finite R (M ⊞ N : ModuleCat.{u} R) := by
  let e : (M ⊞ N : ModuleCat.{u} R) ≃ₗ[R] (M × N) := (ModuleCat.biprodIsoProd M N).toLinearEquiv
  exact ⟨Module.Free.of_equiv e.symm, Module.Finite.equiv e.symm⟩

/-- 写像錐の項は自由・有限を保つ。 -/
lemma mappingCone_free_finite {X Y : CochainComplex (ModuleCat.{u} R) ℤ} (f : X ⟶ Y) (i : ℤ)
    [Module.Free R (X.X (i + 1))] [Module.Free R (Y.X i)]
    [Module.Finite R (X.X (i + 1))] [Module.Finite R (Y.X i)] :
    Module.Free R ((CochainComplex.mappingCone f).X i) ∧
      Module.Finite R ((CochainComplex.mappingCone f).X i) := by
  let e := (HomologicalComplex.homotopyCofiber.XIsoBiprod f i (i + 1) rfl).toLinearEquiv
  obtain ⟨h1, h2⟩ := free_finite_biprod (X.X (i + 1)) (Y.X i)
  exact ⟨Module.Free.of_equiv e.symm, Module.Finite.equiv e.symm⟩

/-- Noether 環上、各項が有限生成な複体のホモロジーは有限生成。 -/
lemma homology_moduleFinite [IsNoetherianRing R] (P : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ)
    [Module.Finite R (P.X i)] : Module.Finite R (P.homology i) := by
  let S := P.sc i
  have : Module.Finite R S.X₂ := inferInstanceAs (Module.Finite R (P.X i))
  have : Module.Finite R S.moduleCatLeftHomologyData.H := by
    change Module.Finite R (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles)
    infer_instance
  exact Module.Finite.equiv S.moduleCatHomologyIso.toLinearEquiv.symm

end SerrePositivity

end
