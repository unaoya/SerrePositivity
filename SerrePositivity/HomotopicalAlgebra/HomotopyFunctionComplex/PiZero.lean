module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionCylinder
public import Mathlib.AlgebraicTopology.SimplicialSet.PiZero
public import Mathlib.AlgebraicTopology.ModelCategory.FundamentalLemma

/-! # Connected components of resolution Hom and ordinary localization

The map is induced by the actual zero-simplices. Edges are homotopies
relative to the constructed good cylinder, and the converse uses the
model-category comparison of homotopies with a fixed good cylinder.
-/

@[expose] public section
universe v u v' u'
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Reedy

namespace SerrePositivity.HomotopyFunctionComplex
variable {C : Type u} [Category.{v} C] [ModelCategory C] (A : SimplexCategory ⥤ C)
  (hconst : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (A.map f))

def edgeLeftHomotopy {Y : C} {f g : A.obj (SimplexCategory.mk 0) ⟶ Y}
    (e : ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj Y).Edge f g) :
    (cosimplicialCylinder A hconst).LeftHomotopy f g where
  h := e.edge
  h₀ := e.src_eq
  h₁ := e.tgt_eq

def piZeroToLeftHomotopyClass (Y : C) :
    SSet.π₀ ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj Y) → LeftHomotopyClass (A.obj (SimplexCategory.mk 0)) Y :=
  SSet.π₀.lift LeftHomotopyClass.mk (fun _ _ e ↦
    LeftHomotopyClass.sound (edgeLeftHomotopy A hconst e).leftHomotopyRel)

@[simp]
lemma piZeroToLeftHomotopyClass_mk {Y : C} (f : A.obj (SimplexCategory.mk 0) ⟶ Y) :
    piZeroToLeftHomotopyClass A hconst Y (SSet.π₀.mk f) = LeftHomotopyClass.mk f := rfl

include hconst in
lemma piZeroToLeftHomotopyClass_bijective
    (hA : reedyLeft simplex (cofibrations C) (initial.to A))
    [IsCofibrant (A.obj (SimplexCategory.mk 0))] (Y : C) [IsFibrant Y] :
    Function.Bijective (piZeroToLeftHomotopyClass A hconst Y) := by
  have := cosimplicialCylinder_isGood A hA hconst
  constructor
  · intro x y h
    obtain ⟨f, rfl⟩ := SSet.π₀.mk_surjective x
    obtain ⟨g, rfl⟩ := SSet.π₀.mk_surjective y
    have hh : LeftHomotopyRel f g :=
      (LeftHomotopyClass.mk_eq_mk_iff (X := A.obj (SimplexCategory.mk 0)) f g).mp h
    let hom := LeftHomotopyRel.leftHomotopy (X := A.obj (SimplexCategory.mk 0))
      (Y := Y) hh (cosimplicialCylinder A hconst)
    apply SSet.π₀.sound
    exact SSet.Edge.ofTruncated { edge := hom.h, src_eq := hom.h₀, tgt_eq := hom.h₁ }
  · intro x
    obtain ⟨f, rfl⟩ := LeftHomotopyClass.mk_surjective x
    exact ⟨SSet.π₀.mk f, rfl⟩

def piZeroLeftHomotopyEquiv
    (hA : reedyLeft simplex (cofibrations C) (initial.to A))
    [IsCofibrant (A.obj (SimplexCategory.mk 0))] (Y : C) [IsFibrant Y] :
    SSet.π₀ ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj Y) ≃ LeftHomotopyClass (A.obj (SimplexCategory.mk 0)) Y :=
  Equiv.ofBijective _ (piZeroToLeftHomotopyClass_bijective A hconst hA Y)

variable {H : Type u'} [Category.{v'} H] (L : C ⥤ H)
  [L.IsLocalization (weakEquivalences C)]

def piZeroLocalizationEquiv
    (hA : reedyLeft simplex (cofibrations C) (initial.to A))
    [IsCofibrant (A.obj (SimplexCategory.mk 0))] (Y : C) [IsFibrant Y] :
    SSet.π₀ ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj Y) ≃ (L.obj (A.obj (SimplexCategory.mk 0)) ⟶ L.obj Y) :=
  (piZeroLeftHomotopyEquiv A hconst hA Y).trans
    (Equiv.ofBijective (leftHomotopyClassToHom L) (bijective_leftHomotopyClassToHom L _ _))

@[simp]
lemma piZeroLocalizationEquiv_mk
    (hA : reedyLeft simplex (cofibrations C) (initial.to A))
    [IsCofibrant (A.obj (SimplexCategory.mk 0))] {Y : C} [IsFibrant Y]
    (f : A.obj (SimplexCategory.mk 0) ⟶ Y) :
    piZeroLocalizationEquiv A hconst L hA Y (SSet.π₀.mk f) = L.map f := rfl

def resolutionZeroLocalizationIso {X : C} (q : CofibrantResolution simplex X) :
    L.obj (q.obj.obj (SimplexCategory.mk 0)) ≅ L.obj X := by
  have : IsIso (L.map (q.augmentation.app (SimplexCategory.mk 0))) :=
    Localization.inverts L (weakEquivalences C) _ (q.augmentation_weakEquivalence _)
  exact asIso (L.map (q.augmentation.app (SimplexCategory.mk 0)))

def resolutionZeroLocalizationNatIso (q : CofibrantResolutionFamily (C := C) simplex) :
    q.obj ⋙ (evaluation SimplexCategory C).obj (SimplexCategory.mk 0) ⋙ L ≅ L :=
  NatIso.ofComponents (fun X ↦ resolutionZeroLocalizationIso L (q.atObject X)) (by
    intro X Z f
    have h := congr_app (q.augmentation.naturality f) (SimplexCategory.mk 0)
    change (q.obj.map f).app (SimplexCategory.mk 0) ≫
        (q.augmentation.app Z).app (SimplexCategory.mk 0) =
      (q.augmentation.app X).app (SimplexCategory.mk 0) ≫ f at h
    exact (L.map_comp _ _).symm.trans ((congrArg L.map h).trans (L.map_comp _ _)))

def resolutionPiZeroLocalizationEquiv {X : C} (q : CofibrantResolution simplex X)
    (Y : C) [IsFibrant Y] :
    SSet.π₀ ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom q.obj).obj Y) ≃ (L.obj X ⟶ L.obj Y) := by
  have := q.isCofibrant_obj (SimplexCategory.mk 0)
  exact (piZeroLocalizationEquiv q.obj q.homotopicallyConstant L q.cofibrant Y).trans
    (Iso.homCongr (resolutionZeroLocalizationIso L q) (Iso.refl _))

@[simp]
lemma resolutionPiZeroLocalizationEquiv_mk {X : C} (q : CofibrantResolution simplex X)
    {Y : C} [IsFibrant Y] (f : q.obj.obj (SimplexCategory.mk 0) ⟶ Y) :
    resolutionPiZeroLocalizationEquiv L q Y (SSet.π₀.mk f) =
      (resolutionZeroLocalizationIso L q).inv ≫ L.map f := by
  change (resolutionZeroLocalizationIso L q).inv ≫ (L.map f ≫ 𝟙 _) = _
  exact congrArg (fun g ↦ (resolutionZeroLocalizationIso L q).inv ≫ g) (Category.comp_id _)

def fibrantTargetLocalizationIso
    (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
    (Y : C) : L.obj Y ≅ L.obj ((fibrantTarget fib).obj Y) := by
  have : IsIso (L.map ((fibrantTargetComparison fib).app Y)) :=
    Localization.inverts L (weakEquivalences C) _ (fibrantTargetComparison_weakEquivalence fib Y)
  exact asIso (L.map ((fibrantTargetComparison fib).app Y))

def fibrantTargetLocalizationNatIso
    (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C)) :
    L ≅ fibrantTarget fib ⋙ L :=
  NatIso.ofComponents (fibrantTargetLocalizationIso L fib) (by
    intro X Z f
    exact (L.map_comp _ _).symm.trans
      ((congrArg L.map ((fibrantTargetComparison fib).naturality f)).trans
        (L.map_comp _ _)))

def chosenResolutionHomPiZeroEquiv
    (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
    (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
    (X : Cᵒᵖ) (Y : C) :
    SSet.π₀ (((chosenResolutionHom cof fib).obj X).obj Y) ≃ (L.obj X.unop ⟶ L.obj Y) := by
  have := fibrantTarget_isFibrant fib Y
  exact (resolutionPiZeroLocalizationEquiv L ((cosimplicialResolutionFamily cof).atObject X.unop)
    ((fibrantTarget fib).obj Y)).trans
      (Iso.homCongr (Iso.refl _) (fibrantTargetLocalizationIso L fib Y).symm)

@[simp]
lemma chosenResolutionHomPiZeroEquiv_mk
    (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
    (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
    (X : Cᵒᵖ) (Y : C)
    (f : ((cosimplicialResolutionFamily cof).obj.obj X.unop).obj (SimplexCategory.mk 0) ⟶
      (fibrantTarget fib).obj Y) :
    chosenResolutionHomPiZeroEquiv L cof fib X Y (SSet.π₀.mk f) =
      (resolutionZeroLocalizationIso L ((cosimplicialResolutionFamily cof).atObject X.unop)).inv ≫
        L.map f ≫ (fibrantTargetLocalizationIso L fib Y).inv := by
  change 𝟙 _ ≫ ((resolutionZeroLocalizationIso L
    ((cosimplicialResolutionFamily cof).atObject X.unop)).inv ≫ (L.map f ≫ 𝟙 _)) ≫ _ = _
  rw [Category.id_comp, Category.comp_id, Category.assoc]
  rfl

lemma chosenResolutionHomPiZeroEquiv_naturality_source
    (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
    (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
    {X X' : Cᵒᵖ} (f : X ⟶ X') (Y : C)
    (z : SSet.π₀ (((chosenResolutionHom cof fib).obj X).obj Y)) :
    chosenResolutionHomPiZeroEquiv L cof fib X' Y
        (SSet.mapπ₀ (((chosenResolutionHom cof fib).map f).app Y) z) =
      L.map f.unop ≫ chosenResolutionHomPiZeroEquiv L cof fib X Y z := by
  obtain ⟨h, rfl⟩ := SSet.π₀.mk_surjective z
  change ((cosimplicialResolutionFamily cof).obj.obj X.unop).obj (SimplexCategory.mk 0) ⟶
    (fibrantTarget fib).obj Y at h
  change chosenResolutionHomPiZeroEquiv L cof fib X' Y
      (SSet.π₀.mk (((cosimplicialResolutionFamily cof).obj.map f.unop).app
        (SimplexCategory.mk 0) ≫ h)) = _
  have hn := (resolutionZeroLocalizationNatIso L (cosimplicialResolutionFamily cof)).inv.naturality
    f.unop
  have hn' : (resolutionZeroLocalizationIso L
      ((cosimplicialResolutionFamily cof).atObject X'.unop)).inv ≫
        L.map (((cosimplicialResolutionFamily cof).obj.map f.unop).app (SimplexCategory.mk 0)) =
      L.map f.unop ≫ (resolutionZeroLocalizationIso L
        ((cosimplicialResolutionFamily cof).atObject X.unop)).inv := hn.symm
  refine (chosenResolutionHomPiZeroEquiv_mk L cof fib X' Y _).trans ?_
  refine Eq.trans ?_ (congrArg (fun k ↦ L.map f.unop ≫ k)
    (chosenResolutionHomPiZeroEquiv_mk L cof fib X Y h).symm)
  refine (congrArg (fun k ↦ (resolutionZeroLocalizationIso L
    ((cosimplicialResolutionFamily cof).atObject X'.unop)).inv ≫ k ≫
      (fibrantTargetLocalizationIso L fib Y).inv)
        (L.map_comp (((cosimplicialResolutionFamily cof).obj.map f.unop).app
          (SimplexCategory.mk 0)) h)).trans ?_
  exact (congrArg (fun k ↦ (resolutionZeroLocalizationIso L
    ((cosimplicialResolutionFamily cof).atObject X'.unop)).inv ≫ k)
      (Category.assoc _ _ _)).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun k ↦ k ≫ L.map h ≫ (fibrantTargetLocalizationIso L fib Y).inv) hn').trans
          (Category.assoc _ _ _)))

lemma chosenResolutionHomPiZeroEquiv_naturality_target
    (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
    (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
    (X : Cᵒᵖ) {Y Y' : C} (f : Y ⟶ Y')
    (z : SSet.π₀ (((chosenResolutionHom cof fib).obj X).obj Y)) :
    chosenResolutionHomPiZeroEquiv L cof fib X Y'
        (SSet.mapπ₀ (((chosenResolutionHom cof fib).obj X).map f) z) =
      chosenResolutionHomPiZeroEquiv L cof fib X Y z ≫ L.map f := by
  obtain ⟨h, rfl⟩ := SSet.π₀.mk_surjective z
  change ((cosimplicialResolutionFamily cof).obj.obj X.unop).obj (SimplexCategory.mk 0) ⟶
    (fibrantTarget fib).obj Y at h
  change chosenResolutionHomPiZeroEquiv L cof fib X Y'
    (SSet.π₀.mk (h ≫ (fibrantTarget fib).map f)) = _
  have hn := (fibrantTargetLocalizationNatIso L fib).inv.naturality f
  have hn' : L.map ((fibrantTarget fib).map f) ≫ (fibrantTargetLocalizationIso L fib Y').inv =
      (fibrantTargetLocalizationIso L fib Y).inv ≫ L.map f := hn
  refine (chosenResolutionHomPiZeroEquiv_mk L cof fib X Y' _).trans ?_
  refine Eq.trans ?_ (congrArg (fun k ↦ k ≫ L.map f)
    (chosenResolutionHomPiZeroEquiv_mk L cof fib X Y h).symm)
  refine (congrArg (fun k ↦ (resolutionZeroLocalizationIso L
    ((cosimplicialResolutionFamily cof).atObject X.unop)).inv ≫ k ≫
      (fibrantTargetLocalizationIso L fib Y').inv)
        (L.map_comp h ((fibrantTarget fib).map f))).trans ?_
  exact (congrArg (fun k ↦ (resolutionZeroLocalizationIso L
    ((cosimplicialResolutionFamily cof).atObject X.unop)).inv ≫ k)
      (Category.assoc _ _ _)).trans
      ((congrArg (fun k ↦ (resolutionZeroLocalizationIso L
        ((cosimplicialResolutionFamily cof).atObject X.unop)).inv ≫ L.map h ≫ k) hn').trans
        ((congrArg (fun k ↦ (resolutionZeroLocalizationIso L
          ((cosimplicialResolutionFamily cof).atObject X.unop)).inv ≫ k)
            (Category.assoc _ _ _).symm).trans (Category.assoc _ _ _).symm))

end SerrePositivity.HomotopyFunctionComplex
