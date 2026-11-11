module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FiniteTensorWeakEquivalence
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.TensorKanCriterion
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.SimplexResolution
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ChosenResolutionHom

/-! # Actual horn tensors for cosimplicial resolutions

A horn has a finite cover by faces with all intersections nonempty faces.
The finite cover gluing theorem proves its tensor inclusion is a weak
equivalence. Reedy cofibrancy supplies the cofibration part independently.
-/

@[expose] public section
universe v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Reedy
open scoped SSet.modelCategoryQuillen

namespace SerrePositivity.HomotopyFunctionComplex
namespace HornCover

lemma inf_faces {n : ℕ} (s : Finset (Fin (n + 1))) :
    s.inf (fun j ↦ SSet.stdSimplex.face.{v} {j}ᶜ) = SSet.stdSimplex.face sᶜ := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.inf_insert, ih, SSet.stdSimplex.face_inter_face]
    congr 1
    ext x
    simp

lemma face_isStandardSimplex {n : ℕ} (s : Finset (Fin (n + 1))) (hs : s.Nonempty) :
    FiniteTensor.IsStandardSimplex (SSet.stdSimplex.face.{v} s).toSSet := by
  obtain ⟨m, hm⟩ : ∃ m, s.card = m + 1 :=
    Nat.exists_eq_succ_of_ne_zero (ne_of_gt (Finset.card_pos.mpr hs))
  exact ⟨SimplexCategory.mk m, ⟨SSet.stdSimplex.isoOfRepresentableBy
    (SSet.stdSimplex.faceRepresentableBy s m (s.orderIsoOfFin hm))⟩⟩

lemma horn_eq_sup {n : ℕ} (i : Fin (n + 1)) :
    SSet.horn.{v} n i = ({i}ᶜ : Finset _).sup
      (fun j ↦ SSet.stdSimplex.face {j}ᶜ) := by
  apply le_antisymm
  · rw [SSet.horn_eq_iSup, iSup_le_iff]
    intro j
    exact Finset.le_sup (f := fun j ↦ SSet.stdSimplex.face.{v} {j}ᶜ)
      (Finset.mem_compl.mpr (fun h ↦ j.property (Finset.mem_singleton.mp h)))
  · apply Finset.sup_le
    intro j hj
    exact SSet.face_le_horn j i (by simpa using hj)

end HornCover

variable {C : Type u} [Category.{v} C] [ModelCategory C] (A : SimplexCategory ⥤ C)

lemma finiteTensor_horn_trivialCofibration
    (hA : reedyLeft simplex (cofibrations C) (initial.to A))
    (hconst : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (A.map f))
    (n : ℕ) (i : Fin (n + 2)) :
    trivialCofibrations C (FiniteTensor.map A (SSet.horn.{v} (n + 1) i).ι) := by
  refine ⟨FiniteTensor.map_mono_cofibration A hA _, ?_⟩
  let U := fun j : Fin (n + 2) ↦ SSet.stdSimplex.face.{v} {j}ᶜ
  let s : Finset (Fin (n + 2)) := {i}ᶜ
  have hs : s.Nonempty := Finset.card_pos.mp (by
    dsimp [s]
    rw [Finset.card_compl]
    simp)
  have hrep (t : Finset (Fin (n + 2))) (ht : t ⊆ s) :
      FiniteTensor.IsStandardSimplex (⊤ ⊓ t.inf U).toSSet := by
    rw [top_inf_eq, HornCover.inf_faces]
    apply HornCover.face_isStandardSimplex
    exact ⟨i, Finset.mem_compl.mpr (fun hi ↦ by
      have := ht hi
      simp [s] at this)⟩
  have h := FiniteTensor.map_finite_cover_weakEquivalence A hconst hA U s ⊤ hs hrep
  have heq : (⊤ : (SSet.stdSimplex.{v}.obj (SimplexCategory.mk (n + 1))).Subcomplex) ⊓
      s.sup U = SSet.horn (n + 1) i :=
    (top_inf_eq _).trans (HornCover.horn_eq_sup i).symm
  let e := SSet.Subcomplex.eqToIso heq
  let eTop := SSet.Subcomplex.topIso
    (SSet.stdSimplex.{v}.obj (SimplexCategory.mk (n + 1)))
  have : IsIso (FiniteTensor.map A e.inv) :=
    inferInstanceAs (IsIso (FiniteTensor.iso A e.symm).hom)
  have : IsIso (FiniteTensor.map A eTop.hom) :=
    inferInstanceAs (IsIso (FiniteTensor.iso A eTop).hom)
  let j := SSet.Subcomplex.homOfLE (inf_le_left : ⊤ ⊓ s.sup U ≤ ⊤)
  have hh : e.inv ≫ j ≫ eTop.hom = (SSet.horn.{v} (n + 1) i).ι := by
    ext m x
    rfl
  have hc := (weakEquivalences C).comp_mem _ _
    ((weakEquivalences C).of_isIso (FiniteTensor.map A e.inv))
    ((weakEquivalences C).comp_mem _ _ h
      ((weakEquivalences C).of_isIso (FiniteTensor.map A eTop.hom)))
  have hm : FiniteTensor.map A e.inv ≫
      (FiniteTensor.map A j ≫ FiniteTensor.map A eTop.hom) =
        FiniteTensor.map A (SSet.horn.{v} (n + 1) i).ι :=
    (congrArg (fun f ↦ FiniteTensor.map A e.inv ≫ f)
      (FiniteTensor.map_comp A j eTop.hom)).trans
      ((FiniteTensor.map_comp A e.inv (j ≫ eTop.hom)).trans
        (congrArg (FiniteTensor.map A) hh))
  exact hm ▸ hc

lemma hornTensor_trivialCofibration
    (hA : reedyLeft simplex (cofibrations C) (initial.to A))
    (hconst : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (A.map f))
    (n : ℕ) (i : Fin (n + 2)) :
    trivialCofibrations C (SubcomplexTensor.inclusion (SSet.horn.{v} (n + 1) i) A) :=
  ((trivialCofibrations C).arrow_iso_iff (finiteTensorInclusionArrowIso A _)).mp
    (finiteTensor_horn_trivialCofibration A hA hconst n i)

lemma cosimplicialHom_kanComplex
    (hA : reedyLeft simplex (cofibrations C) (initial.to A))
    (hconst : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (A.map f))
    (Y : C) [IsFibrant Y] : SSet.KanComplex ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj Y) :=
  kanComplex_of_hornTensors A (hornTensor_trivialCofibration A hA hconst) Y

lemma cosimplicialHom_fibration
    (hA : reedyLeft simplex (cofibrations C) (initial.to A))
    (hconst : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (A.map f))
    {Y Z : C} (p : Y ⟶ Z) [Fibration p] : Fibration ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).map p) :=
  fibration_of_hornTensors A (hornTensor_trivialCofibration A hA hconst) p

lemma cosimplicialResolution_hom_kanComplex (X Y : C) [IsFibrant Y] :
    SSet.KanComplex ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (cosimplicialResolution X).obj).obj Y) :=
  cosimplicialHom_kanComplex _ (cosimplicialResolution X).cofibrant
    (cosimplicialResolution X).homotopicallyConstant Y

lemma chosenResolutionHom_kanComplex
    (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
    (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
    (X : Cᵒᵖ) (Y : C) : SSet.KanComplex (((chosenResolutionHom cof fib).obj X).obj Y) := by
  have := fibrantTarget_isFibrant fib Y
  exact cosimplicialHom_kanComplex _ ((cosimplicialResolutionFamily cof).cofibrant X.unop)
    ((cosimplicialResolutionFamily cof).atObject X.unop).homotopicallyConstant _

end SerrePositivity.HomotopyFunctionComplex
