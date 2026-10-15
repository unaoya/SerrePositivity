module

public import Mathlib.AlgebraicTopology.ModelCategory.Cylinder
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # A cylinder quotient as a cofiber of a contractible cone

Collapse the first endpoint of a cylinder to zero. The remaining endpoint
is a cobase change of the two-endpoint inclusion. For a good cylinder on a
cofibrant object this is a cofibration, and the cone is weakly zero. These
facts hold in any pointed model category, with no properness or generation
assumptions. They reduce the cylinder quotient to an ordinary suspension
span with one contractible leaf.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped ZeroObject

namespace SerrePositivity.ModelCylinder
variable {C : Type u} [Category.{v} C] [HasFiniteColimits C]
  [HasZeroObject C] [HasZeroMorphisms C] [ModelCategory C]
  {X : C} (P : Cylinder X)

def cone : C := pushout P.i₀ (0 : X ⟶ 0)

abbrev coneInclusion : P.I ⟶ cone P := pushout.inl P.i₀ (0 : X ⟶ 0)
abbrev coneBasepoint : (0 : C) ⟶ cone P := pushout.inr P.i₀ (0 : X ⟶ 0)
def coneEndpoint : X ⟶ cone P := P.i₁ ≫ coneInclusion P
def boundaryProjection (_P : Cylinder X) : X ⨿ X ⟶ X := coprod.desc (0 : X ⟶ X) (𝟙 X)

lemma firstEndpoint_coneInclusion : P.i₀ ≫ coneInclusion P = 0 := by
  simpa using (pushout.condition (f := P.i₀) (g := (0 : X ⟶ (0 : C))))

lemma coneBoundary_condition : P.i ≫ coneInclusion P = boundaryProjection P ≫ coneEndpoint P := by
  apply coprod.hom_ext
  · simp [Precylinder.i, boundaryProjection, firstEndpoint_coneInclusion]
  · simp [Precylinder.i, boundaryProjection, coneEndpoint]

def coneBoundaryIsColimit : IsColimit (PushoutCocone.mk
    (coneInclusion P) (coneEndpoint P) (coneBoundary_condition P)) := by
  refine PushoutCocone.IsColimit.mk (coneBoundary_condition P) ?_ ?_ ?_ ?_
  · intro s
    exact pushout.desc s.inl 0 (by
      have h := congrArg (fun f ↦ coprod.inl ≫ f) s.condition
      simpa [Precylinder.i, boundaryProjection] using h)
  · intro s
    exact pushout.inl_desc ..
  · intro s
    have h := congrArg (fun f ↦ coprod.inr ≫ f) s.condition
    simpa [Precylinder.i, boundaryProjection, coneEndpoint] using h
  · intro s m hm _
    apply pushout.hom_ext
    · simpa only [pushout.inl_desc] using hm
    · exact (isZero_zero C).eq_of_src _ _

lemma coneBoundary_isPushout : IsPushout P.i (boundaryProjection P)
    (coneInclusion P) (coneEndpoint P) where
  w := coneBoundary_condition P
  isColimit' := ⟨coneBoundaryIsColimit P⟩

section Quotient
variable {S : C} (q : P.I ⟶ S)
  (sq : IsPushout P.i (0 : X ⨿ X ⟶ (0 : C)) q (0 : (0 : C) ⟶ S))

include sq in
lemma firstEndpoint_quotient : P.i₀ ≫ q = 0 := by
  have h := congrArg (fun f ↦ coprod.inl ≫ f) sq.w
  simpa [Precylinder.i] using h

include sq in
lemma secondEndpoint_quotient : P.i₁ ≫ q = 0 := by
  have h := congrArg (fun f ↦ coprod.inr ≫ f) sq.w
  simpa [Precylinder.i] using h

def coneQuotient : cone P ⟶ S :=
  pushout.desc q 0 (by simpa using firstEndpoint_quotient P q sq)

@[reassoc (attr := simp)] lemma coneInclusion_coneQuotient :
    coneInclusion P ≫ coneQuotient P q sq = q := pushout.inl_desc ..

lemma coneEndpoint_coneQuotient : coneEndpoint P ≫ coneQuotient P q sq = 0 := by
  rw [coneEndpoint, Category.assoc, coneInclusion_coneQuotient, secondEndpoint_quotient P q sq]

lemma coneQuotient_isPushout : IsPushout (coneEndpoint P) (0 : X ⟶ (0 : C))
    (coneQuotient P q sq) (0 : (0 : C) ⟶ S) := by
  have houter : IsPushout P.i (boundaryProjection P ≫ (0 : X ⟶ (0 : C)))
      (coneInclusion P ≫ coneQuotient P q sq) (0 : (0 : C) ⟶ S) := by
    simpa only [comp_zero, coneInclusion_coneQuotient] using sq
  exact houter.of_top (by simp [coneEndpoint_coneQuotient]) (coneBoundary_isPushout P)
end Quotient

variable [IsCofibrant X] [P.IsGood]

omit [IsCofibrant X] in
lemma coneEndpoint_cofibration : Cofibration (coneEndpoint P) :=
  ⟨(cofibrations C).of_isPushout (coneBoundary_isPushout P).flip (mem_cofibrations P.i)⟩

lemma coneCollapse_weakEquivalence : WeakEquivalence (0 : cone P ⟶ (0 : C)) := by
  have hb : weakEquivalences C (coneBasepoint P) :=
    ((trivialCofibrations C).of_isPushout (IsPushout.of_hasPushout P.i₀ (0 : X ⟶ (0 : C))).flip
      (mem_trivialCofibrations P.i₀)).2
  constructor
  apply (weakEquivalences C).of_precomp (coneBasepoint P) _ hb
  have h : coneBasepoint P ≫ (0 : cone P ⟶ (0 : C)) = 𝟙 (0 : C) :=
    (isZero_zero C).eq_of_src _ _
  rw [h]
  exact (weakEquivalences C).id_mem _

end SerrePositivity.ModelCylinder
