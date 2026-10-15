module

public import SerrePositivity.HomotopicalAlgebra.Diagram.YonedaWeights
public import SerrePositivity.HomotopicalAlgebra.Diagram.ConstantWeightRealization
public import Mathlib.CategoryTheory.HomCongr

/-! # Realizing the universal Yoneda weight diagram

The unit copower weight at k represents degree-zero evaluation at k under
frame-weight realization. The resulting isomorphism is natural in k.
-/

@[expose] public section
universe w u
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open SerrePositivity.HomotopyFunctionComplex

namespace SerrePositivity.DiagramModel.YonedaWeightRealization
variable (K : Type w) [SmallCategory K] {C : Type u} [Category.{w} C]
  [HasColimitsOfSize.{w, w} C] (A : K ⥤ SimplexCategory ⥤ C)

abbrev weightFamily : K ⥤ Kᵒᵖ ⥤ SSet.{w} := YonedaWeights.family K (𝟙_ SSet.{w})

def weightHomEquiv (k : K) (Y : C) :
    ((weightFamily K).obj k ⟶ (FrameWeightRealization.hom K A).obj Y) ≃
      ((A.obj k).obj (SimplexCategory.mk 0) ⟶ Y) :=
  ((YonedaWeights.freeWeightIso K (𝟙_ SSet.{w}) k).homCongr (Iso.refl _)).trans
    (((evaluationAdjunctionRight SSet.{w} (Opposite.op k)).homEquiv _ _).trans
      ((ConstantWeightRealization.unitSimplexIso.homCongr (Iso.refl _)).trans
        SSet.yonedaEquiv))

omit [HasColimitsOfSize.{w, w} C] in
lemma weightHomEquiv_target_naturality (k : K) {Y Z : C} (f : Y ⟶ Z)
    (a : (weightFamily K).obj k ⟶ (FrameWeightRealization.hom K A).obj Y) :
    weightHomEquiv K A k Z (a ≫ (FrameWeightRealization.hom K A).map f) =
      weightHomEquiv K A k Y a ≫ f := by
  rfl

set_option backward.isDefEq.respectTransparency false in
omit [HasColimitsOfSize.{w, w} C] in
lemma weightHomEquiv_apply (k : K) (Y : C)
    (a : (weightFamily K).obj k ⟶ (FrameWeightRealization.hom K A).obj Y) :
    weightHomEquiv K A k Y a = SSet.yonedaEquiv
      (ConstantWeightRealization.unitSimplexIso.inv ≫
        Sigma.ι (fun _ : k ⟶ k => 𝟙_ SSet.{w}) (𝟙 k) ≫ a.app (Opposite.op k)) := by
  change SSet.yonedaEquiv (ConstantWeightRealization.unitSimplexIso.inv ≫
    (Sigma.ι (fun _ : Opposite.op k ⟶ Opposite.op k => 𝟙_ SSet.{w}) (𝟙 _) ≫
      Sigma.map' (fun h : Opposite.op k ⟶ Opposite.op k => h.unop)
        (fun _ => 𝟙 (𝟙_ SSet.{w})) ≫ a.app (Opposite.op k))) = _
  rw [Sigma.ι_comp_map'_assoc]
  rfl

omit [HasColimitsOfSize.{w, w} C] in
lemma weightHomEquiv_source_naturality {k l : K} (g : k ⟶ l) (Y : C)
    (a : (weightFamily K).obj l ⟶ (FrameWeightRealization.hom K A).obj Y) :
    weightHomEquiv K A k Y ((weightFamily K).map g ≫ a) =
      (A.map g).app (SimplexCategory.mk 0) ≫ weightHomEquiv K A l Y a := by
  rw [weightHomEquiv_apply, weightHomEquiv_apply]
  have h := congrArg
    (fun z => ConstantWeightRealization.unitSimplexIso.inv ≫
      Sigma.ι (fun _ : l ⟶ l => 𝟙_ SSet.{w}) (𝟙 l) ≫ z) (a.naturality g.op)
  have he : ConstantWeightRealization.unitSimplexIso.inv ≫
      Sigma.ι (fun _ : k ⟶ k => 𝟙_ SSet.{w}) (𝟙 k) ≫
        (((weightFamily K).map g ≫ a).app (Opposite.op k)) =
      (ConstantWeightRealization.unitSimplexIso.inv ≫
        Sigma.ι (fun _ : l ⟶ l => 𝟙_ SSet.{w}) (𝟙 l) ≫ a.app (Opposite.op l)) ≫
          ((FrameWeightRealization.hom K A).obj Y).map g.op := by
    change ConstantWeightRealization.unitSimplexIso.inv ≫
      Sigma.ι (fun _ : k ⟶ k => 𝟙_ SSet.{w}) (𝟙 k) ≫
        (Sigma.map' (fun h : k ⟶ k => h ≫ g) (fun _ => 𝟙 (𝟙_ SSet.{w})) ≫
          a.app (Opposite.op k)) = _
    simpa [weightFamily, YonedaWeights.family, Category.assoc] using h
  rw [he, SSet.yonedaEquiv_comp]
  rfl

def homEquiv (k : K) (Y : C) :
    ((FrameWeightRealization.functor K A).obj ((weightFamily K).obj k) ⟶ Y) ≃
      ((A.obj k).obj (SimplexCategory.mk 0) ⟶ Y) :=
  ((FrameWeightRealization.adjunction K A).homEquiv _ Y).trans (weightHomEquiv K A k Y)

lemma homEquiv_target_naturality (k : K) {Y Z : C} (f : Y ⟶ Z)
    (a : (FrameWeightRealization.functor K A).obj ((weightFamily K).obj k) ⟶ Y) :
    homEquiv K A k Z (a ≫ f) = homEquiv K A k Y a ≫ f := by
  dsimp [homEquiv]
  rw [Adjunction.homEquiv_naturality_right, weightHomEquiv_target_naturality]

lemma homEquiv_source_naturality {k l : K} (g : k ⟶ l) (Y : C)
    (a : (FrameWeightRealization.functor K A).obj ((weightFamily K).obj l) ⟶ Y) :
    homEquiv K A k Y ((FrameWeightRealization.functor K A).map ((weightFamily K).map g) ≫ a) =
      (A.map g).app (SimplexCategory.mk 0) ≫ homEquiv K A l Y a := by
  unfold homEquiv
  simp only [Equiv.trans_apply]
  rw [(FrameWeightRealization.adjunction K A).homEquiv_naturality_left,
    weightHomEquiv_source_naturality]

def coyonedaIso (k : K) :
    coyoneda.obj (Opposite.op ((FrameWeightRealization.functor K A).obj
      ((weightFamily K).obj k))) ≅
        coyoneda.obj (Opposite.op ((A.obj k).obj (SimplexCategory.mk 0))) :=
  NatIso.ofComponents (fun Y => Equiv.toIso (homEquiv K A k Y)) (by
    intro Y Z f
    ext a
    exact homEquiv_target_naturality K A k f a)

def objIso (k : K) :
    (FrameWeightRealization.functor K A).obj ((weightFamily K).obj k) ≅
      (A.obj k).obj (SimplexCategory.mk 0) :=
  (Coyoneda.fullyFaithful.preimageIso (coyonedaIso K A k)).unop.symm

lemma objIso_inv_comp (k : K) (Y : C)
    (a : (FrameWeightRealization.functor K A).obj ((weightFamily K).obj k) ⟶ Y) :
    (objIso K A k).inv ≫ a = homEquiv K A k Y a := by
  have h := Coyoneda.fullyFaithful.map_preimage (coyonedaIso K A k).hom
  exact congrArg (fun z => z.app Y a) h

def iso : weightFamily K ⋙ FrameWeightRealization.functor K A ≅
    ConstantWeightHom.degree K A (SimplexCategory.mk 0) :=
  NatIso.ofComponents (objIso K A) (by
    intro k l g
    change (FrameWeightRealization.functor K A).map ((weightFamily K).map g) ≫
      (objIso K A l).hom = (objIso K A k).hom ≫ (A.map g).app (SimplexCategory.mk 0)
    apply (homEquiv K A k _).injective
    rw [homEquiv_source_naturality, homEquiv_target_naturality]
    rw [← objIso_inv_comp, ← objIso_inv_comp]
    simp)

end SerrePositivity.DiagramModel.YonedaWeightRealization
