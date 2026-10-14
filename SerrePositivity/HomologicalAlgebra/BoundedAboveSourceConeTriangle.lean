module
public import SerrePositivity.HomologicalAlgebra.BoundedAboveDerivedConeTriangle
public import SerrePositivity.HomologicalAlgebra.BoundedAboveDerivedAdditive

/-! # Source cone triangles of bounded-above projective representatives -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe v u v' u'
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits HomologicalComplex Pretriangulated
attribute [local instance] HasDerivedCategory.standard
variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughProjectives C]

/-- The cone triangle with the original derived objects as its first two vertices. -/
def boundedAboveSourceConeTriangle {X Y : DerivedCategory.Minus C} (f : X ⟶ Y) :
    Triangle (DerivedCategory C) :=
  let P := boundedAboveDerivedChosenModel X
  let Q := boundedAboveDerivedChosenModel Y
  let h := P.map Q f.hom
  Triangle.mk f.hom (boundedAboveDerivedConeInr P Q h).hom
    ((boundedAboveDerivedConeProjection P Q h).hom ≫
      (DerivedCategory.Minus.ι.commShiftIso (1 : ℤ)).hom.app X)

/-- The source cone triangle agrees with the standard cone of the lifted chain map. -/
def boundedAboveSourceConeTriangleIso {X Y : DerivedCategory.Minus C} (f : X ⟶ Y) :
    boundedAboveSourceConeTriangle f ≅
      DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle
        ((boundedAboveDerivedChosenModel X).map (boundedAboveDerivedChosenModel Y) f.hom)) := by
  let P := boundedAboveDerivedChosenModel X
  let Q := boundedAboveDerivedChosenModel Y
  let h := P.map Q f.hom
  refine Triangle.isoMk _ _ P.iso.symm Q.iso.symm (Iso.refl _) ?_ ?_ ?_
  · change f.hom ≫ Q.iso.inv = P.iso.inv ≫ DerivedCategory.Q.map h
    rw [P.map_Q Q f.hom]
    simp
  · simp [boundedAboveSourceConeTriangle, boundedAboveDerivedConeInr, Q]
  · change ((boundedAboveDerivedConeProjection P Q h).hom ≫
      (DerivedCategory.Minus.ι.commShiftIso (1 : ℤ)).hom.app X) ≫
        P.iso.inv⟦(1 : ℤ)⟧' =
      𝟙 _ ≫ (DerivedCategory.Q.map (CochainComplex.mappingCone.triangle h).mor₃ ≫
        (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app P.complex)
    simp [boundedAboveDerivedConeProjection, BoundedAboveDerivedModel.shiftMinus,
      BoundedAboveDerivedModel.transport, BoundedAboveDerivedModel.shift, Category.assoc,
      ← Functor.map_comp]

lemma boundedAboveSourceConeTriangle_distinguished {X Y : DerivedCategory.Minus C}
    (f : X ⟶ Y) : boundedAboveSourceConeTriangle f ∈ distTriang (DerivedCategory C) :=
  isomorphic_distinguished _ (DerivedCategory.mappingCone_triangle_distinguished _) _
    (boundedAboveSourceConeTriangleIso f)

/-- Any distinguished triangle on the same first morphism is isomorphic to the source cone. -/
def boundedAboveSourceConeTriangleIsoOfDistinguished {X Y : DerivedCategory.Minus C}
    (f : X ⟶ Y) (Z : DerivedCategory C) (g : Y.obj ⟶ Z) (δ : Z ⟶ X.obj⟦(1 : ℤ)⟧)
    (hT : Triangle.mk f.hom g δ ∈ distTriang (DerivedCategory C)) :
    boundedAboveSourceConeTriangle f ≅ Triangle.mk f.hom g δ :=
  isoTriangleOfIso₁₂ _ _ (boundedAboveSourceConeTriangle_distinguished f) hT
    (Iso.refl _) (Iso.refl _) (by simp [boundedAboveSourceConeTriangle])

variable {E : Type u'} [Category.{v'} E] [Abelian E]

/-- Apply the actual left derived functor to all three arrows, using its shift comparison. -/
def boundedAboveLeftDerivedTriangle (F : C ⥤ E) [F.Additive]
    {X Y Z : DerivedCategory.Minus C} (f : X ⟶ Y) (g : Y ⟶ Z) (δ : Z ⟶ X⟦(1 : ℤ)⟧) :
    Triangle (DerivedCategory E) :=
  Triangle.mk ((boundedAboveLeftDerived F).map f).hom ((boundedAboveLeftDerived F).map g).hom
    (((boundedAboveLeftDerived F).map δ).hom ≫ (boundedAboveLeftDerivedShiftIso F X 1).hom)

/-- Every bounded-above distinguished triangle gives a distinguished left-derived image. -/
lemma boundedAboveLeftDerivedTriangle_distinguished (F : C ⥤ E) [F.Additive]
    {X Y Z : DerivedCategory.Minus C} (f : X ⟶ Y) (g : Y ⟶ Z) (δ : Z ⟶ X⟦(1 : ℤ)⟧)
    (hT : Triangle.mk f.hom g.hom
      (δ.hom ≫ (DerivedCategory.Minus.ι.commShiftIso (1 : ℤ)).hom.app X) ∈
        distTriang (DerivedCategory C)) :
    boundedAboveLeftDerivedTriangle F f g δ ∈ distTriang (DerivedCategory E) := by
  let P := boundedAboveDerivedChosenModel X
  let Q := boundedAboveDerivedChosenModel Y
  let h := P.map Q f.hom
  let e := boundedAboveSourceConeTriangleIsoOfDistinguished f Z.obj g.hom
    (δ.hom ≫ (DerivedCategory.Minus.ι.commShiftIso (1 : ℤ)).hom.app X) hT
  let k : boundedAboveDerivedConeObject P Q h ≅ Z :=
    ObjectProperty.isoMk _ (Triangle.π₃.mapIso e)
  have hg : boundedAboveDerivedConeInr P Q h ≫ k.hom = g := by
    apply InducedCategory.hom_ext
    have he := e.hom.comm₂
    simpa [e, k, boundedAboveSourceConeTriangleIsoOfDistinguished,
      boundedAboveSourceConeTriangle, P, Q, h] using he
  have hδ : boundedAboveDerivedConeProjection P Q h = k.hom ≫ δ := by
    apply InducedCategory.hom_ext
    apply (cancel_mono ((DerivedCategory.Minus.ι.commShiftIso (1 : ℤ)).hom.app X)).mp
    have he := e.hom.comm₃
    simpa [e, k, boundedAboveSourceConeTriangleIsoOfDistinguished,
      boundedAboveSourceConeTriangle, P, Q, h, Category.assoc] using he
  let ek : ((boundedAboveLeftDerived F).obj (boundedAboveDerivedConeObject P Q h)).obj ≅
      ((boundedAboveLeftDerived F).obj Z).obj :=
    DerivedCategory.Minus.ι.mapIso ((boundedAboveLeftDerived F).mapIso k)
  have ei : boundedAboveLeftDerivedConeTriangle F f ≅
      boundedAboveLeftDerivedTriangle F f g δ := by
    refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) ek
      (by simp [boundedAboveLeftDerivedConeTriangle, boundedAboveLeftDerivedTriangle]) ?_ ?_
    · change ((boundedAboveLeftDerived F).map (boundedAboveDerivedConeInr P Q h)).hom ≫
        ((boundedAboveLeftDerived F).map k.hom).hom = 𝟙 _ ≫ _
      rw [← ObjectProperty.FullSubcategory.comp_hom, ← Functor.map_comp, hg, Category.id_comp]
      rfl
    · change (((boundedAboveLeftDerived F).map (boundedAboveDerivedConeProjection P Q h)).hom ≫
        (boundedAboveLeftDerivedShiftIso F X 1).hom) ≫ (𝟙 _)⟦(1 : ℤ)⟧' =
          ((boundedAboveLeftDerived F).map k.hom).hom ≫
            (((boundedAboveLeftDerived F).map δ).hom ≫ _)
      rw [hδ, Functor.map_comp]
      simp [Category.assoc]
  exact isomorphic_distinguished _ (boundedAboveLeftDerivedConeTriangle_distinguished F f) _ ei.symm

/-- Homology exactness for any bounded-above distinguished triangle after left derivation. -/
lemma boundedAboveLeftDerivedTriangle_homology_exact (F : C ⥤ E) [F.Additive]
    {X Y Z : DerivedCategory.Minus C} (f : X ⟶ Y) (g : Y ⟶ Z) (δ : Z ⟶ X⟦(1 : ℤ)⟧)
    (hT : Triangle.mk f.hom g.hom
      (δ.hom ≫ (DerivedCategory.Minus.ι.commShiftIso (1 : ℤ)).hom.app X) ∈
        distTriang (DerivedCategory C)) (i : ℤ) :
    ((shortComplexOfDistTriangle (boundedAboveLeftDerivedTriangle F f g δ)
      (boundedAboveLeftDerivedTriangle_distinguished F f g δ hT)).map
        (DerivedCategory.homologyFunctor E i)).Exact :=
  (DerivedCategory.homologyFunctor E i).map_distinguished_exact _
    (boundedAboveLeftDerivedTriangle_distinguished F f g δ hT)

end SerrePositivity
