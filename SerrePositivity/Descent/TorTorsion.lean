module

public import SerrePositivity.KoszulBaseChange
public import SerrePositivity.Tor
public import Mathlib.Algebra.Homology.Linear
public import Mathlib.Algebra.Homology.ShortComplex.Linear
public import Mathlib.Algebra.Homology.Single
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution

/-!
# `Tor` と消去イデアル

`a ∈ A` が `V` 上で零なら、`φ a` は `Tor_i^A(V, C)`（`TorAlg φ i V`）上で零。

証明：`a • 𝟙 V = 0` なので `(F.leftDerived i).map (a • 𝟙 V) = (F.leftDerived i).map 0 = 0`。
一方、射影分解 `P` の上では `a • 𝟙 P` が `a • 𝟙 V` を持ち上げるので、
`Functor.leftDerived_map_eq` により `(F.leftDerived i).map (a • 𝟙 V)` は
`H_i(F(a • 𝟙 P)) = H_i(φ a • 𝟙) = φ a • 𝟙` と同型で移り合う。
よって `φ a • 𝟙 = 0`。

途中で使う補題：`single`、係数拡大 `F.mapHomologicalComplex`、`homologyMap` が
それぞれスカラー倍と両立すること（任意の複体の形で）。`notes/PLAN.md` §11 の B3。
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace SerrePositivity

section general

variable {R : Type u} [CommRing R] {ι : Type*} {c : ComplexShape ι}

/-- `homologyMap` はスカラー倍と両立する（任意の複体の形）。 -/
lemma homologyMap_smul' {K L : HomologicalComplex (ModuleCat.{u} R) c} (f : K ⟶ L) (a : R)
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

end general

variable {A C : Type u} [CommRing A] [CommRing C] (φ : A →+* C)

/-- 係数拡大は複体の射のスカラー倍を `φ` 倍に送る（任意の複体の形）。 -/
lemma extendScalars_mapHomologicalComplex_smul {ι : Type*} {c : ComplexShape ι}
    {K L : HomologicalComplex (ModuleCat.{u} A) c} (f : K ⟶ L) (a : A) :
    ((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex c).map (a • f) =
      φ a • ((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex c).map f := by
  ext i
  simp [extendScalars_map_smul]

/-- `a` が `V` を消すなら `φ a` は `Tor_i^A(V, C)` を消す。 -/
theorem torAlg_smul_eq_zero (i : ℕ) (V : Type u) [AddCommGroup V] [Module A V] (a : A)
    (ha : ∀ v : V, a • v = 0) (x : TorAlg φ i V) : φ a • x = 0 := by
  let F := ModuleCat.extendScalars.{u, u, u} φ
  let X := ModuleCat.of A V
  let P := projectiveResolution X
  have hf : (a • 𝟙 X : X ⟶ X) = 0 := ModuleCat.hom_ext (LinearMap.ext ha)
  have hw : (a • 𝟙 P.complex) ≫ P.π =
      P.π ≫ (ChainComplex.single₀ (ModuleCat.{u} A)).map (a • 𝟙 X) := by
    rw [single_map_smul, CategoryTheory.Functor.map_id, Linear.smul_comp, Linear.comp_smul,
      Category.id_comp, Category.comp_id]
  have h1 := F.leftDerived_map_eq i (a • 𝟙 X) (P := P) (Q := P) (a • 𝟙 P.complex) hw
  have h2 : (F.mapHomologicalComplex _ ⋙ HomologicalComplex.homologyFunctor _ _ i).map
      (a • 𝟙 P.complex) = φ a • 𝟙 _ := by
    rw [Functor.comp_map, extendScalars_mapHomologicalComplex_smul, CategoryTheory.Functor.map_id,
      HomologicalComplex.homologyFunctor_map, homologyMap_smul', HomologicalComplex.homologyMap_id]
    rfl
  have h3 : (F.leftDerived i).map (a • 𝟙 X) = φ a • 𝟙 _ := by
    rw [h1, h2, Linear.smul_comp, Linear.comp_smul]
    erw [Category.id_comp]
    rw [Iso.hom_inv_id]
  have h4 : (F.leftDerived i).map (a • 𝟙 X) = 0 := by
    rw [hf, F.leftDerived_map_eq i (0 : X ⟶ X) (P := P) (Q := P) 0 (by simp), Functor.map_zero]
    erw [Limits.zero_comp]
    rw [Limits.comp_zero]
  have h5 : (φ a • 𝟙 ((F.leftDerived i).obj X) : _ ⟶ _) = 0 := h3.symm.trans h4
  have := congrArg (fun g : (F.leftDerived i).obj X ⟶ (F.leftDerived i).obj X ↦ g.hom x) h5
  simpa using this

end SerrePositivity
