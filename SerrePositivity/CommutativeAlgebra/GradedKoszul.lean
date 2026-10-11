module

public import SerrePositivity.CommutativeAlgebra.GradedKoszulHomology
public import SerrePositivity.CommutativeAlgebra.ReesModuleGrading
public import SerrePositivity.CommutativeAlgebra.KoszulReesFinite
public import SerrePositivity.HomologicalAlgebra.KoszulRestriction

/-!
# Gradings on Koszul complexes of Rees modules

The coefficient grading is put on each term of the iterated scalar cone.
Differentials raise this coefficient degree by one. Internal Koszul degree
`n` in cochain position `q` is obtained by the shift `n + q`.
-/

@[expose] public noncomputable section

universe u

namespace SerrePositivity.GradedKoszul

open CategoryTheory Limits
open HomologicalComplex.homotopyCofiber
open SerrePositivity.HilbertSerre SerrePositivity.HilbertSamuel
open scoped DirectSum

set_option backward.isDefEq.respectTransparency false


section complexes

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- A Koszul complex with an arbitrary coefficient module. -/
abbrev moduleComplex {h : ℕ} (x : Fin h → S) (M : ModuleCat.{u} S) :=
  (koszulModuleFunctor x).obj M

/-- The complex viewed over the coefficient ring `R`. -/
abbrev restrictComplex (P : CochainComplex (ModuleCat.{u} S) ℤ) :=
  ((ModuleCat.restrictScalars (algebraMap R S)).mapHomologicalComplex (.up ℤ)).obj
    P

/-- Restrict the Koszul module complex to the coefficient ring. -/
abbrev underlyingComplex {h : ℕ} (x : Fin h → S) (M : ModuleCat.{u} S) :=
  restrictComplex (R := R) (moduleComplex x M)

/-- Scalar multiplication by an element of `S`, viewed as an `R`-linear map. -/
def scalarOnModule (b : S) (M : ModuleCat.{u} S) :
    (ModuleCat.restrictScalars (algebraMap R S)).obj M →ₗ[R]
      (ModuleCat.restrictScalars (algebraMap R S)).obj M :=
  ((ModuleCat.restrictScalars (algebraMap R S)).map (b • 𝟙 M)).hom

/-- Restriction of an `S`-linear isomorphism still commutes with `S`-scalars. -/
theorem mapIso_scalar_eq {M N : ModuleCat.{u} S} (e : M ≅ N) (b : S)
    (u : (ModuleCat.restrictScalars (algebraMap R S)).obj M) :
    ((ModuleCat.restrictScalars (algebraMap R S)).mapIso e).toLinearEquiv
        (scalarOnModule (R := R) b M u) =
      scalarOnModule (R := R) b N
        (((ModuleCat.restrictScalars (algebraMap R S)).mapIso e).toLinearEquiv u) :=
  e.toLinearEquiv.map_smul b u

/-- The two-product description of a scalar cone term after restriction. -/
def coneTermEquiv (a : S) (P : CochainComplex (ModuleCat.{u} S) ℤ) (q : ℤ) :
    (ModuleCat.restrictScalars (algebraMap R S)).obj (((scalarConeFunctor a).obj P).X q) ≃ₗ[R]
      ((ModuleCat.restrictScalars (algebraMap R S)).obj (P.X (q + 1))) ×
        ((ModuleCat.restrictScalars (algebraMap R S)).obj (P.X q)) :=
  ((ModuleCat.restrictScalars (algebraMap R S)).mapIso (scalarConeXIsoProd a P q)).toLinearEquiv

/-- The cone product coordinates commute with scalar multiplication. -/
theorem coneTermEquiv_scalar (a b : S) (P : CochainComplex (ModuleCat.{u} S) ℤ)
    (q : ℤ)
    (u : (ModuleCat.restrictScalars (algebraMap R S)).obj (((scalarConeFunctor a).obj P).X q)) :
    coneTermEquiv (R := R) a P q
        (scalarOnModule (R := R) b (((scalarConeFunctor a).obj P).X q) u) =
      (scalarOnModule (R := R) b (P.X (q + 1)) (coneTermEquiv (R := R) a P q u).1,
        scalarOnModule (R := R) b (P.X q) (coneTermEquiv (R := R) a P q u).2) :=
  (scalarConeXIsoProd a P q).toLinearEquiv.map_smul b u

private theorem scalarConeXIsoProd_fst (a : S) (P : CochainComplex (ModuleCat.{u} S) ℤ)
    (q : ℤ) :
    (scalarConeXIsoProd a P q).hom ≫ ModuleCat.ofHom (LinearMap.fst S (P.X (q + 1)) (P.X q)) =
      fstX (smulId a P) q (q + 1) rfl := by
  have hb : (ModuleCat.biprodIsoProd (P.X (q + 1)) (P.X q)).hom ≫
      ModuleCat.ofHom (LinearMap.fst S (P.X (q + 1)) (P.X q)) = biprod.fst := by
    apply (cancel_epi (ModuleCat.biprodIsoProd (P.X (q + 1)) (P.X q)).inv).mp
    rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp,
      ModuleCat.biprodIsoProd_inv_comp_fst]
  dsimp only [scalarConeXIsoProd, Iso.trans_hom]
  rw [Category.assoc, hb]
  rfl

private theorem scalarConeXIsoProd_snd (a : S) (P : CochainComplex (ModuleCat.{u} S) ℤ)
    (q : ℤ) :
    (scalarConeXIsoProd a P q).hom ≫ ModuleCat.ofHom (LinearMap.snd S (P.X (q + 1)) (P.X q)) =
      sndX (smulId a P) q := by
  have hb : (ModuleCat.biprodIsoProd (P.X (q + 1)) (P.X q)).hom ≫
      ModuleCat.ofHom (LinearMap.snd S (P.X (q + 1)) (P.X q)) = biprod.snd := by
    apply (cancel_epi (ModuleCat.biprodIsoProd (P.X (q + 1)) (P.X q)).inv).mp
    rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp,
      ModuleCat.biprodIsoProd_inv_comp_snd]
  dsimp only [scalarConeXIsoProd, Iso.trans_hom]
  rw [Category.assoc, hb]
  apply ext_from_X (smulId a P) (q + 1) q rfl
  · simp only [← Category.assoc, inlX_XIsoBiprod_hom, biprod.inl_snd, inlX_sndX]
  · simp only [← Category.assoc, inrX_XIsoBiprod_hom, biprod.inr_snd, inrX_sndX]

/-- The first component of the cone differential is the negative old differential. -/
theorem coneTermEquiv_d_fst (a : S) (P : CochainComplex (ModuleCat.{u} S) ℤ) (q : ℤ)
    (u : (ModuleCat.restrictScalars (algebraMap R S)).obj (((scalarConeFunctor a).obj P).X q)) :
    (coneTermEquiv (R := R) a P (q + 1)
      (((ModuleCat.restrictScalars (algebraMap R S)).map
        (((scalarConeFunctor a).obj P).d q (q + 1))).hom u)).1 =
      - (((ModuleCat.restrictScalars (algebraMap R S)).map (P.d (q + 1) (q + 1 + 1))).hom
        (coneTermEquiv (R := R) a P q u).1) := by
  have h := d_fstX (smulId a P) q (q + 1) (q + 1 + 1) rfl rfl
  rw [← scalarConeXIsoProd_fst a P (q + 1), ← scalarConeXIsoProd_fst a P q] at h
  exact congrArg (fun f => f.hom u) h

/-- The second component adds scalar multiplication to the old differential. -/
theorem coneTermEquiv_d_snd (a : S) (P : CochainComplex (ModuleCat.{u} S) ℤ) (q : ℤ)
    (u : (ModuleCat.restrictScalars (algebraMap R S)).obj (((scalarConeFunctor a).obj P).X q)) :
    (coneTermEquiv (R := R) a P (q + 1)
      (((ModuleCat.restrictScalars (algebraMap R S)).map
        (((scalarConeFunctor a).obj P).d q (q + 1))).hom u)).2 =
      ((ModuleCat.restrictScalars (algebraMap R S)).map (a • 𝟙 (P.X (q + 1)))).hom
        (coneTermEquiv (R := R) a P q u).1 +
      ((ModuleCat.restrictScalars (algebraMap R S)).map (P.d q (q + 1))).hom
        (coneTermEquiv (R := R) a P q u).2 := by
  have h := d_sndX (smulId a P) q (q + 1) rfl
  rw [← scalarConeXIsoProd_snd a P (q + 1), ← scalarConeXIsoProd_fst a P q,
    ← scalarConeXIsoProd_snd a P q] at h
  exact congrArg (fun f => f.hom u) h

/-- The coefficient grading on every term, recursively along the cone model. -/
def termGrade : ∀ {h : ℕ} (x : Fin h → S) (M : ModuleCat.{u} S),
    (ℕ → Submodule R ((ModuleCat.restrictScalars (algebraMap R S)).obj M)) →
      (q : ℤ) → ℕ → Submodule R ((underlyingComplex (R := R) x M).X q)
  | 0, _, M, N, q, n => if hq : q = 0 then
      (N n).map (((ModuleCat.restrictScalars (algebraMap R S)).mapIso
        (HomologicalComplex.singleObjXIsoOfEq (.up ℤ) 0 M q hq)).toLinearEquiv.symm.toLinearMap)
      else ⊥
  | h + 1, x, M, N, q, n =>
      ((termGrade (Fin.init x) M N (q + 1) n).prod (termGrade (Fin.init x) M N q n)).map
        (coneTermEquiv (R := R) (x (Fin.last h)) (moduleComplex (Fin.init x) M) q).symm.toLinearMap

/-- Every term has its coefficient decomposition. -/
theorem isInternal_termGrade : ∀ {h : ℕ} (x : Fin h → S) (M : ModuleCat.{u} S)
    (N : ℕ → Submodule R ((ModuleCat.restrictScalars (algebraMap R S)).obj M))
    [DirectSum.Decomposition N] (q : ℤ),
    DirectSum.IsInternal (termGrade x M N q)
  | 0, x, M, N, _, q => by
    by_cases hq : q = 0
    · simp only [termGrade, dite_eq_left hq]
      exact isInternal_map_equiv N _
    · have hz : IsZero ((moduleComplex x M).X q) :=
        HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 M q hq
      have hz' := (ModuleCat.restrictScalars (algebraMap R S)).map_isZero hz
      have : Subsingleton ((underlyingComplex (R := R) x M).X q) :=
        ModuleCat.isZero_iff_subsingleton.mp hz'
      simp only [termGrade, dite_eq_right hq]
      exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun m => ⟨0, Subsingleton.elim _ _⟩⟩
  | h + 1, x, M, N, _, q => by
    let : DirectSum.Decomposition (termGrade (Fin.init x) M N (q + 1)) :=
      (isInternal_termGrade (Fin.init x) M N (q + 1)).chooseDecomposition
    let : DirectSum.Decomposition (termGrade (Fin.init x) M N q) :=
      (isInternal_termGrade (Fin.init x) M N q).chooseDecomposition
    let : DirectSum.Decomposition (fun n =>
        (termGrade (Fin.init x) M N (q + 1) n).prod (termGrade (Fin.init x) M N q n)) :=
      (isInternal_prod _ _).chooseDecomposition
    exact isInternal_map_equiv _
      (coneTermEquiv (R := R) (x (Fin.last h)) (moduleComplex (Fin.init x) M) q).symm

/-- A scalar of coefficient degree one raises every term grade by one. -/
theorem scalarOnModule_mem_termGrade {h : ℕ} (x : Fin h → S) (M : ModuleCat.{u} S)
    (N : ℕ → Submodule R ((ModuleCat.restrictScalars (algebraMap R S)).obj M))
    (b : S) (hb : ∀ n, ∀ u ∈ N n, scalarOnModule (R := R) b M u ∈ N (n + 1))
    (q : ℤ) (n : ℕ) (u : (underlyingComplex (R := R) x M).X q)
    (hu : u ∈ termGrade x M N q n) :
    scalarOnModule (R := R) b ((moduleComplex x M).X q) u ∈ termGrade x M N q (n + 1) := by
  induction h generalizing q with
  | zero =>
    by_cases hq : q = 0
    · simp only [termGrade, dite_eq_left hq, Submodule.map_equiv_eq_comap_symm,
        LinearEquiv.symm_symm, Submodule.mem_comap] at hu ⊢
      have he := mapIso_scalar_eq (R := R)
        (HomologicalComplex.singleObjXIsoOfEq (.up ℤ) 0 M q hq) b u
      exact he.symm ▸ hb n _ hu
    · simp only [termGrade, dite_eq_right hq, Submodule.mem_bot] at hu ⊢
      rw [hu, map_zero]
  | succ h ih =>
    simp only [termGrade, Submodule.map_equiv_eq_comap_symm, LinearEquiv.symm_symm,
      Submodule.mem_comap, Submodule.mem_prod] at hu ⊢
    have he := coneTermEquiv_scalar (R := R) (x (Fin.last h)) b
      (moduleComplex (Fin.init x) M) q u
    exact ⟨(congrArg Prod.fst he).symm ▸ ih (Fin.init x) (q + 1) _ hu.1,
      (congrArg Prod.snd he).symm ▸ ih (Fin.init x) q _ hu.2⟩

/-- The differential raises the coefficient degree by one; after the Koszul
shift, it preserves internal degree. -/
theorem differential_mem_termGrade {h : ℕ} (x : Fin h → S) (M : ModuleCat.{u} S)
    (N : ℕ → Submodule R ((ModuleCat.restrictScalars (algebraMap R S)).obj M))
    (hx : ∀ j n, ∀ u ∈ N n, scalarOnModule (R := R) (x j) M u ∈ N (n + 1))
    (q : ℤ) (n : ℕ) (u : (underlyingComplex (R := R) x M).X q)
    (hu : u ∈ termGrade x M N q n) :
    ((underlyingComplex (R := R) x M).d q (q + 1)).hom u ∈
      termGrade x M N (q + 1) (n + 1) := by
  induction h generalizing q with
  | zero =>
    change ((ModuleCat.restrictScalars (algebraMap R S)).map
      (((HomologicalComplex.single _ (.up ℤ) 0).obj M).d q (q + 1))).hom u ∈ _
    rw [HomologicalComplex.single_obj_d, Functor.map_zero]
    exact Submodule.zero_mem _
  | succ h ih =>
    have hinit : ∀ j n, ∀ u ∈ N n,
        scalarOnModule (R := R) (Fin.init x j) M u ∈ N (n + 1) :=
      fun j => hx j.castSucc
    simp only [termGrade, Submodule.map_equiv_eq_comap_symm, LinearEquiv.symm_symm,
      Submodule.mem_comap, Submodule.mem_prod] at hu ⊢
    have he1 := coneTermEquiv_d_fst (R := R) (x (Fin.last h))
      (moduleComplex (Fin.init x) M) q u
    have he2 := coneTermEquiv_d_snd (R := R) (x (Fin.last h))
      (moduleComplex (Fin.init x) M) q u
    refine ⟨he1.symm ▸ Submodule.neg_mem _ (ih (Fin.init x) hinit (q + 1) _ hu.1), ?_⟩
    have hs := scalarOnModule_mem_termGrade (Fin.init x) M N (x (Fin.last h))
      (hx (Fin.last h)) (q + 1) n _ hu.1
    have hd := ih (Fin.init x) hinit q _ hu.2
    exact he2.symm ▸ (termGrade (Fin.init x) M N (q + 1) (n + 1)).add_mem hs hd

end complexes

end SerrePositivity.GradedKoszul
