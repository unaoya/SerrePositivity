module

public import SerrePositivity.KTheory.Adams.KoszulCubeFourierOneCoordinates
public import SerrePositivity.KTheory.Adams.KoszulCubeFourierTwoCoordinates

/-! # Degreewise Fourier basis isomorphisms for a Koszul cube -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory Category Limits HomologicalComplex Preadditive
variable {R : Type u} [CommRing R] [Invertible (3 : R)]
namespace Adams

def oneKoszulCubeFourierOneBasisIso (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    (tensorCube (oneKoszulComplex a)).X (-1) ≅
      ModuleCat.of R R ⊞ (ModuleCat.of R R ⊞ ModuleCat.of R R) where
  hom := biprod.lift (oneKoszulCubeFourierOneZeroCoordinate a)
    (biprod.lift (oneKoszulCubeFourierOneOneCoordinate a t) (oneKoszulCubeFourierOneTwoCoordinate
      a t))
  inv := biprod.desc (oneKoszulCubeFourierOneZero a)
    (biprod.desc (oneKoszulCubeFourierOneOne a t) (oneKoszulCubeFourierOneTwo a t))
  hom_inv_id := by
    apply oneKoszulCubeXNegOne_hom_ext a
    · simpa [Category.assoc, biprod.lift_desc,
        oneKoszulCubeFourierOneZeroCoordinate,
        oneKoszulCubeFourierOneOneCoordinate,
        oneKoszulCubeFourierOneTwoCoordinate,
        comp_add, comp_sub, Linear.comp_smul, Linear.smul_comp,
        smul_add, smul_sub, ← neg_smul, neg_sub, neg_add_rev, neg_neg, sub_eq_add_neg, add_assoc]
          using
        (oneKoszulCubeE0_fourier a t ht).symm
    · simpa [Category.assoc, biprod.lift_desc,
        oneKoszulCubeFourierOneZeroCoordinate,
        oneKoszulCubeFourierOneOneCoordinate,
        oneKoszulCubeFourierOneTwoCoordinate,
        comp_add, comp_sub, Linear.comp_smul, Linear.smul_comp,
        smul_add, smul_sub, ← neg_smul, neg_sub, neg_add_rev, neg_neg, sub_eq_add_neg, add_assoc]
          using
        (oneKoszulCubeE1_fourier a t ht).symm
    · simpa [Category.assoc, biprod.lift_desc,
        oneKoszulCubeFourierOneZeroCoordinate,
        oneKoszulCubeFourierOneOneCoordinate,
        oneKoszulCubeFourierOneTwoCoordinate,
        comp_add, comp_sub, Linear.comp_smul, Linear.smul_comp,
        smul_add, smul_sub, ← neg_smul, neg_sub, neg_add_rev, neg_neg, sub_eq_add_neg, add_assoc]
          using
        (oneKoszulCubeE2_fourier a t ht).symm
  inv_hom_id := by
    apply biprod.hom_ext
    · apply biprod.hom_ext'
      · simp [Category.assoc]
      · apply biprod.hom_ext'
        · simp [Category.assoc, ht]
        · simp [Category.assoc, ht]
    · apply biprod.hom_ext
      · apply biprod.hom_ext'
        · simp [Category.assoc, ht]
        · apply biprod.hom_ext'
          · simp [Category.assoc, ht]
          · simp [Category.assoc, ht]
      · apply biprod.hom_ext'
        · simp [Category.assoc, ht]
        · apply biprod.hom_ext'
          · simp [Category.assoc, ht]
          · simp [Category.assoc, ht]

def oneKoszulCubeFourierTwoBasisIso (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    (tensorCube (oneKoszulComplex a)).X (-2) ≅
      ModuleCat.of R R ⊞ (ModuleCat.of R R ⊞ ModuleCat.of R R) where
  hom := biprod.lift (oneKoszulCubeFourierTwo01Coordinate a t)
    (biprod.lift (oneKoszulCubeFourierTwo02Coordinate a t) (oneKoszulCubeFourierTwo12Coordinate a
      t))
  inv := biprod.desc (oneKoszulCubeFourierTwo01 a t)
    (biprod.desc (oneKoszulCubeFourierTwo02 a t) (oneKoszulCubeFourierTwo12 a t))
  hom_inv_id := by
    apply oneKoszulCubeXNegTwo_hom_ext a
    · simpa [Category.assoc, biprod.lift_desc,
        oneKoszulCubeFourierTwo01Coordinate,
        oneKoszulCubeFourierTwo02Coordinate,
        oneKoszulCubeFourierTwo12Coordinate,
        comp_add, comp_sub, Linear.comp_smul, Linear.smul_comp,
        smul_add, smul_sub, ← neg_smul, neg_sub, neg_add_rev, neg_neg, sub_eq_add_neg, add_assoc]
          using
        (oneKoszulCubeE01_fourier a t ht).symm
    · simpa [Category.assoc, biprod.lift_desc,
        oneKoszulCubeFourierTwo01Coordinate,
        oneKoszulCubeFourierTwo02Coordinate,
        oneKoszulCubeFourierTwo12Coordinate,
        comp_add, comp_sub, Linear.comp_smul, Linear.smul_comp,
        smul_add, smul_sub, ← neg_smul, neg_sub, neg_add_rev, neg_neg, sub_eq_add_neg, add_assoc]
          using
        (oneKoszulCubeE02_fourier a t ht).symm
    · simpa [Category.assoc, biprod.lift_desc,
        oneKoszulCubeFourierTwo01Coordinate,
        oneKoszulCubeFourierTwo02Coordinate,
        oneKoszulCubeFourierTwo12Coordinate,
        comp_add, comp_sub, Linear.comp_smul, Linear.smul_comp,
        smul_add, smul_sub, ← neg_smul, neg_sub, neg_add_rev, neg_neg, sub_eq_add_neg, add_assoc]
          using
        (oneKoszulCubeE12_fourier a t ht).symm
  inv_hom_id := by
    apply biprod.hom_ext
    · apply biprod.hom_ext'
      · simp [Category.assoc, ht]
      · apply biprod.hom_ext'
        · simp [Category.assoc, ht]
        · simp [Category.assoc]
    · apply biprod.hom_ext
      · apply biprod.hom_ext'
        · simp [Category.assoc, ht]
        · apply biprod.hom_ext'
          · simp [Category.assoc, ht]
          · simp [Category.assoc]
      · apply biprod.hom_ext'
        · simp [Category.assoc]
        · apply biprod.hom_ext'
          · simp [Category.assoc]
          · simp [Category.assoc, ht]

def oneKoszulCubeFourierTopBasisIso (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    (tensorCube (oneKoszulComplex a)).X (-3) ≅ ModuleCat.of R R where
  hom := oneKoszulCubeFourierTopCoordinate a t
  inv := oneKoszulCubeFourierTop a t
  hom_inv_id := by
    apply oneKoszulCubeXNegThree_hom_ext a
    simpa [oneKoszulCubeFourierTopCoordinate, Category.assoc, Linear.comp_smul,
      Linear.smul_comp] using (oneKoszulCubeTop_fourier a t ht).symm
  inv_hom_id := oneKoszulCubeFourierTop_TopCoordinate a t ht

lemma oneKoszulCubeFourierOne_hom_ext (a t : R) (ht : t ^ 2 + t + 1 = 0)
    {Y : ModuleCat.{u} R} {f g : (tensorCube (oneKoszulComplex a)).X (-1) ⟶ Y}
    (h0 : oneKoszulCubeFourierOneZero a ≫ f = oneKoszulCubeFourierOneZero a ≫ g)
    (h1 : oneKoszulCubeFourierOneOne a t ≫ f = oneKoszulCubeFourierOneOne a t ≫ g)
    (h2 : oneKoszulCubeFourierOneTwo a t ≫ f = oneKoszulCubeFourierOneTwo a t ≫ g)
    : f = g := by
  apply oneKoszulCubeXNegOne_hom_ext a
  · simp only [oneKoszulCubeE0_fourier a t ht, add_comp,
      h0, h1, h2]
  · simp only [oneKoszulCubeE1_fourier a t ht, add_comp,
      Linear.smul_comp, h0, h1, h2]
  · simp only [oneKoszulCubeE2_fourier a t ht, add_comp,
      Linear.smul_comp, h0, h1, h2]
lemma oneKoszulCubeFourierTwo_hom_ext (a t : R) (ht : t ^ 2 + t + 1 = 0)
    {Y : ModuleCat.{u} R} {f g : (tensorCube (oneKoszulComplex a)).X (-2) ⟶ Y}
    (h0 : oneKoszulCubeFourierTwo01 a t ≫ f = oneKoszulCubeFourierTwo01 a t ≫ g)
    (h1 : oneKoszulCubeFourierTwo02 a t ≫ f = oneKoszulCubeFourierTwo02 a t ≫ g)
    (h2 : oneKoszulCubeFourierTwo12 a t ≫ f = oneKoszulCubeFourierTwo12 a t ≫ g)
    : f = g := by
  apply oneKoszulCubeXNegTwo_hom_ext a
  · simp only [oneKoszulCubeE01_fourier a t ht, add_comp, sub_comp,
      Linear.smul_comp, h0, h1, h2]
  · simp only [oneKoszulCubeE02_fourier a t ht, add_comp,
      Linear.smul_comp, h0, h1, h2]
  · simp only [oneKoszulCubeE12_fourier a t ht, add_comp, sub_comp,
      Linear.smul_comp, h0, h1, h2]
lemma oneKoszulCubeFourierTop_hom_ext (a t : R) (ht : t ^ 2 + t + 1 = 0)
    {Y : ModuleCat.{u} R} {f g : (tensorCube (oneKoszulComplex a)).X (-3) ⟶ Y}
    (h : oneKoszulCubeFourierTop a t ≫ f = oneKoszulCubeFourierTop a t ≫ g) : f = g := by
  apply oneKoszulCubeXNegThree_hom_ext a
  simp only [oneKoszulCubeTop_fourier a t ht, Linear.smul_comp, h]

end Adams
end SerrePositivity
