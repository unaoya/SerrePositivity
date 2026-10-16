module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarPiZero
public import SerrePositivity.HomotopicalAlgebra.Simplicial.UniverseLiftPiZero

/-! # Every label-preserving stable bar quotient has the same actual components

No finite-boundary lifting condition is needed for this component result.
It does not assert that such a quotient preserves higher homotopy.
-/

@[expose] public section
universe v u vH uH
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryQuotientPiZero
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {H : Type uH} [Category.{vH} H] (Q : C ⥤ H)
  [Q.IsLocalization (weakEquivalences C)]
  (R : DiagramQuotient.Congruence (OrdinaryResolutionBar.functor (C := C)))
  (hR : ∀ b n {x y}, (R.rel b n).r x y →
    OrdinaryBarMappingClasses.label Q b n x = OrdinaryBarMappingClasses.label Q b n y)

def piZeroLabel (b : Cᵒᵖ × C) :
    SSet.π₀ ((DiagramQuotient.functor R).obj b) → LocalizedHomDiagram.value Q b :=
  fun z => (PiZeroConstant.toComponents
    (show (DiagramQuotient.functor R).obj b ⟶
      PiZeroConstant.discrete (ULift.{max u v, v} (LocalizedHomDiagram.value Q b)) from
        (OrdinaryBarMappingClasses.descend Q R hR).app b) z).down

lemma factorization (b : Cᵒᵖ × C)
    (z : SSet.π₀ (OrdinaryResolutionBar.functor.obj b)) :
    piZeroLabel Q R hR b (SSet.mapπ₀ ((DiagramQuotient.projection R).app b) z) =
      OrdinaryBarMappingClasses.piZeroLabel Q b z := by
  obtain ⟨x, rfl⟩ := SSet.π₀.mk_surjective z
  rfl

lemma projection_surjective (b : Cᵒᵖ × C) :
    Function.Surjective (SSet.mapπ₀ ((DiagramQuotient.projection R).app b)) := by
  intro z
  obtain ⟨q, rfl⟩ := SSet.π₀.mk_surjective z
  obtain ⟨x, rfl⟩ := Quotient.exists_rep q
  exact ⟨SSet.π₀.mk x, rfl⟩

lemma label_naturality {b c : Cᵒᵖ × C} (f : b ⟶ c)
    (z : SSet.π₀ ((DiagramQuotient.functor R).obj b)) :
    piZeroLabel Q R hR c (SSet.mapπ₀ ((DiagramQuotient.functor R).map f) z) =
      (LocalizedHomDiagram.types Q).map f (piZeroLabel Q R hR b z) := by
  obtain ⟨q, rfl⟩ := SSet.π₀.mk_surjective z
  obtain ⟨x, rfl⟩ := Quotient.exists_rep q
  exact OrdinaryBarMappingClasses.label_base Q f _ x

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

include hcof hfib in
lemma piZeroLabel_bijective (b : Cᵒᵖ × C) :
    Function.Bijective (piZeroLabel Q R hR b) := by
  constructor
  · intro x y h
    obtain ⟨x, rfl⟩ := projection_surjective R b x
    obtain ⟨y, rfl⟩ := projection_surjective R b y
    rw [factorization, factorization] at h
    exact congrArg (SSet.mapπ₀ ((DiagramQuotient.projection R).app b))
      (OrdinaryBarPiZero.piZeroLabel_injective hcof hfib Q b h)
  · intro z
    obtain ⟨x, hx⟩ := OrdinaryBarLabelSurjectivity.piZeroLabel_surjective Q b z
    exact ⟨SSet.mapπ₀ ((DiagramQuotient.projection R).app b) x,
      (factorization Q R hR b x).trans hx⟩

include Q hR hcof hfib in
lemma projection_bijective (b : Cᵒᵖ × C) :
    Function.Bijective (SSet.mapπ₀ ((DiagramQuotient.projection R).app b)) := by
  refine ⟨fun x y h => OrdinaryBarPiZero.piZeroLabel_injective hcof hfib Q b ?_,
    projection_surjective R b⟩
  exact (factorization Q R hR b x).symm.trans
    ((congrArg (piZeroLabel Q R hR b) h).trans (factorization Q R hR b y))

def piZeroEquiv (b : Cᵒᵖ × C) : SSet.π₀ ((DiagramQuotient.functor R).obj b) ≃
    (Q.obj b.1.unop ⟶ Q.obj b.2) :=
  (Equiv.ofBijective _ (piZeroLabel_bijective Q R hR hcof hfib b)).trans
    (LocalizedHomDiagram.equiv Q b)

lemma piZeroEquiv_naturality {b c : Cᵒᵖ × C} (f : b ⟶ c)
    (z : SSet.π₀ ((DiagramQuotient.functor R).obj b)) :
    piZeroEquiv Q R hR hcof hfib c (SSet.mapπ₀ ((DiagramQuotient.functor R).map f) z) =
      Q.map f.1.unop ≫ piZeroEquiv Q R hR hcof hfib b z ≫ Q.map f.2 := by
  change LocalizedHomDiagram.equiv Q c (piZeroLabel Q R hR c _) = _
  rw [label_naturality, LocalizedHomDiagram.types_map]
  rfl

variable (hsmall : ∀ b n, Small.{v} (Quotient (R.rel b n)))

def smallPiZeroEquiv (b : Cᵒᵖ × C) :
    SSet.π₀ ((SmallDiagramQuotient.functor R hsmall).obj b) ≃
      (Q.obj b.1.unop ⟶ Q.obj b.2) :=
  (UniverseLiftPiZero.equiv.{v, max u v} _).symm.trans
    ((Equiv.ofBijective (SSet.mapπ₀
      ((SmallSimplicialValue.diagramLiftIso (DiagramQuotient.functor R) hsmall).hom.app b))
        ((CategoryTheory.isIso_iff_bijective _).mp
          (inferInstance : IsIso (SSet.π₀Functor.map
            ((SmallSimplicialValue.diagramLiftIso
              (DiagramQuotient.functor R) hsmall).hom.app b))))).trans
      (piZeroEquiv Q R hR hcof hfib b))

lemma smallPiZeroEquiv_naturality {b c : Cᵒᵖ × C} (f : b ⟶ c)
    (z : SSet.π₀ ((SmallDiagramQuotient.functor R hsmall).obj b)) :
    smallPiZeroEquiv Q R hR hcof hfib hsmall c
        (SSet.mapπ₀ ((SmallDiagramQuotient.functor R hsmall).map f) z) =
      Q.map f.1.unop ≫ smallPiZeroEquiv Q R hR hcof hfib hsmall b z ≫ Q.map f.2 := by
  let e := SmallSimplicialValue.diagramLiftIso (DiagramQuotient.functor R) hsmall
  change piZeroEquiv Q R hR hcof hfib c
      (SSet.mapπ₀ (e.hom.app c) (UniverseLiftPiZero.up _ (SSet.mapπ₀ _ z))) = _
  have hn : SSet.uliftFunctor.{max u v, v}.map
      ((SmallDiagramQuotient.functor R hsmall).map f) ≫ e.hom.app c =
        e.hom.app b ≫ (DiagramQuotient.functor R).map f := e.hom.naturality f
  rw [← UniverseLiftPiZero.up_naturality, ← SSet.mapπ₀_comp_apply,
    hn, SSet.mapπ₀_comp_apply]
  exact piZeroEquiv_naturality Q R hR hcof hfib f _

lemma smallProjection_factorization (b : Cᵒᵖ × C)
    (z : SSet.π₀ (OrdinaryResolutionBar.functor.obj b)) :
    smallPiZeroEquiv Q R hR hcof hfib hsmall b
        (UniverseLiftPiZero.down _
          (SSet.mapπ₀ ((SmallDiagramQuotient.projection R hsmall).app b) z)) =
      OrdinaryBarPiZero.piZeroEquiv hcof hfib Q b z := by
  let e := SmallSimplicialValue.diagramLiftIso (DiagramQuotient.functor R) hsmall
  let t := SSet.mapπ₀ ((SmallDiagramQuotient.projection R hsmall).app b) z
  change piZeroEquiv Q R hR hcof hfib b
    (SSet.mapπ₀ (e.hom.app b) (UniverseLiftPiZero.up _ (UniverseLiftPiZero.down _ t))) = _
  rw [show UniverseLiftPiZero.up _ (UniverseLiftPiZero.down _ t) = t from
    (UniverseLiftPiZero.equiv _).symm_apply_apply t]
  have hp : (SmallDiagramQuotient.projection R hsmall).app b ≫ e.hom.app b =
      (DiagramQuotient.projection R).app b := by
    change ((DiagramQuotient.projection R).app b ≫ e.inv.app b) ≫ e.hom.app b = _
    rw [Category.assoc, e.inv_hom_id_app, Category.comp_id]
  change piZeroEquiv Q R hR hcof hfib b (SSet.mapπ₀ (e.hom.app b)
    (SSet.mapπ₀ ((SmallDiagramQuotient.projection R hsmall).app b) z)) = _
  rw [← SSet.mapπ₀_comp_apply, hp]
  change LocalizedHomDiagram.equiv Q b (piZeroLabel Q R hR b _) = _
  rw [factorization]
  rfl

end SerrePositivity.HomotopyFunctionComplex.OrdinaryQuotientPiZero
