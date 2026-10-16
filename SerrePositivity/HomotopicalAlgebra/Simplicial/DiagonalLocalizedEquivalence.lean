module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.DiagonalKanTests
public import SerrePositivity.HomotopicalAlgebra.Simplicial.LocalizedMonoReedy
public import SerrePositivity.HomotopicalAlgebra.Simplicial.BoundaryReedyFactorization

/-! # Rowwise anodyne-localized equivalences are diagonal equivalences in any value universe -/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.Reedy SerrePositivity.SimplicialModel

namespace SerrePositivity.BisimplicialModel

lemma localized_diagonal_map_of_reedyMono {A B : SimplexCategoryᵒᵖ ⥤ SSet.{v}} (f : A ⟶ B)
    (hm : reedyLeft simplexOp (MorphismProperty.monomorphisms _) f)
    (hf : ∀ n, IsIso (AnodyneHomotopy.anodyneQ.map (f.app n))) :
    IsIso (AnodyneHomotopy.anodyneQ.map (diagonal.map f)) :=
  localized_diagonal_map_of_reedy_localizedMonos f ((LocalizedMonoReedy.reedy_iff f).mpr ⟨hm, hf⟩)

lemma localized_diagonal_map {A B : SimplexCategoryᵒᵖ ⥤ SSet.{v}} (f : A ⟶ B)
    (hf : ∀ n, IsIso (AnodyneHomotopy.anodyneQ.map (f.app n))) :
    IsIso (AnodyneHomotopy.anodyneQ.map (diagonal.map f)) := by
  have : MorphismProperty.IsWeakFactorizationSystem BoundaryFactorization.left.{v}
      BoundaryFactorization.right.{v} := BoundaryFactorization.reedy_wfs
  have : BoundaryFactorization.left.{v}.IsMultiplicative := by
    rw [BoundaryFactorization.left_eq_llp]
    infer_instance
  have : BoundaryFactorization.left.{v}.IsStableUnderCobaseChange := by
    rw [BoundaryFactorization.left_eq_llp]
    infer_instance
  let d := MorphismProperty.factorizationData BoundaryFactorization.left
    BoundaryFactorization.right (coprod.desc f (𝟙 B))
  let l := coprod.inl ≫ d.i
  let r := coprod.inr ≫ d.i
  have hlp : l ≫ d.p = f := by
    dsimp only [l]
    rw [Category.assoc, d.fac, coprod.inl_desc]
  have hrp : r ≫ d.p = 𝟙 B := by
    dsimp only [r]
    rw [Category.assoc, d.fac, coprod.inr_desc]
  have hlm : BoundaryFactorization.left l := BoundaryFactorization.left.comp_mem _ _
    (BoundaryFactorization.left.of_isPushout (IsPushout.of_hasBinaryCoproduct' A B)
      (BoundaryFactorization.initial_left B)) d.hi
  have hrm : BoundaryFactorization.left r := BoundaryFactorization.left.comp_mem _ _
    (BoundaryFactorization.left.of_isPushout (IsPushout.of_hasBinaryCoproduct' A B).flip
      (BoundaryFactorization.initial_left A)) d.hi
  have hl : ∀ n, IsIso (AnodyneHomotopy.anodyneQ.map (l.app n)) := by
    intro n
    have : IsIso (AnodyneHomotopy.anodyneQ.map (d.p.app n)) :=
      BoundaryFactorization.right_app_localized d.p d.hp n
    have h := congrArg AnodyneHomotopy.anodyneQ.map (congr_app hlp n)
    rw [NatTrans.comp_app, Functor.map_comp] at h
    have hc : IsIso (AnodyneHomotopy.anodyneQ.map (l.app n) ≫
        AnodyneHomotopy.anodyneQ.map (d.p.app n)) := h.symm ▸ hf n
    exact (isIso_comp_right_iff _ _).mp hc
  have hr : ∀ n, IsIso (AnodyneHomotopy.anodyneQ.map (r.app n)) := by
    intro n
    have : IsIso (AnodyneHomotopy.anodyneQ.map (d.p.app n)) :=
      BoundaryFactorization.right_app_localized d.p d.hp n
    have h := congrArg AnodyneHomotopy.anodyneQ.map (congr_app hrp n)
    rw [NatTrans.comp_app, NatTrans.id_app, Functor.map_comp, CategoryTheory.Functor.map_id] at h
    have hc : IsIso (AnodyneHomotopy.anodyneQ.map (r.app n) ≫
        AnodyneHomotopy.anodyneQ.map (d.p.app n)) := h.symm ▸ inferInstanceAs (IsIso (𝟙 _))
    exact (isIso_comp_right_iff _ _).mp hc
  let Q := diagonal ⋙ AnodyneHomotopy.anodyneQ
  have : IsIso (Q.map l) := localized_diagonal_map_of_reedyMono l hlm hl
  have : IsIso (Q.map r) := localized_diagonal_map_of_reedyMono r hrm hr
  have hp : IsIso (Q.map d.p) := by
    have h := congrArg Q.map hrp
    rw [Q.map_comp, Q.map_id] at h
    have hc : IsIso (Q.map r ≫ Q.map d.p) := h.symm ▸ inferInstanceAs (IsIso (𝟙 _))
    exact (isIso_comp_left_iff _ _).mp hc
  have h := congrArg Q.map hlp
  rw [Q.map_comp] at h
  exact h ▸ inferInstanceAs (IsIso (Q.map l ≫ Q.map d.p))

end SerrePositivity.BisimplicialModel
