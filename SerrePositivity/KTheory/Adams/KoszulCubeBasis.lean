module

public import SerrePositivity.KTheory.Adams.KoszulCubeCoordinates

/-! # Ordered scalar bases for the four nonzero degrees of a Koszul cube -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory Category Limits MonoidalCategory HomologicalComplex
variable {R : Type u} [CommRing R]
namespace Adams

def oneKoszulCubeZeroBasisIso (a : R) :
    (tensorCube (oneKoszulComplex a)).X (0) ≅ ModuleCat.of R R where
  hom := oneKoszulCubeBottomCoordinate a
  inv := oneKoszulCubeBottom a
  hom_inv_id := by
    apply oneKoszulCubeXZero_hom_ext a
    simp
  inv_hom_id := oneKoszulCubeBottom_BottomCoordinate a

def oneKoszulCubeNegThreeBasisIso (a : R) :
    (tensorCube (oneKoszulComplex a)).X (-3) ≅ ModuleCat.of R R where
  hom := oneKoszulCubeTopCoordinate a
  inv := oneKoszulCubeTop a
  hom_inv_id := by
    apply oneKoszulCubeXNegThree_hom_ext a
    simp
  inv_hom_id := oneKoszulCubeTop_TopCoordinate a

def oneKoszulCubeNegOneBasisIso (a : R) :
    (tensorCube (oneKoszulComplex a)).X (-1) ≅
      ModuleCat.of R R ⊞ (ModuleCat.of R R ⊞ ModuleCat.of R R) where
  hom := biprod.lift (oneKoszulCubeE0Coordinate a)
    (biprod.lift (oneKoszulCubeE1Coordinate a) (oneKoszulCubeE2Coordinate a))
  inv := biprod.desc (oneKoszulCubeE0 a)
    (biprod.desc (oneKoszulCubeE1 a) (oneKoszulCubeE2 a))
  hom_inv_id := by
    apply oneKoszulCubeXNegOne_hom_ext a <;> simp [biprod.lift_desc]
  inv_hom_id := by
    apply biprod.hom_ext
    · apply biprod.hom_ext'
      · simp [Category.assoc]
      · apply biprod.hom_ext'
        · simp [Category.assoc]
        · simp [Category.assoc]
    · apply biprod.hom_ext
      · apply biprod.hom_ext'
        · simp [Category.assoc]
        · apply biprod.hom_ext'
          · simp [Category.assoc]
          · simp [Category.assoc]
      · apply biprod.hom_ext'
        · simp [Category.assoc]
        · apply biprod.hom_ext'
          · simp [Category.assoc]
          · simp [Category.assoc]

def oneKoszulCubeNegTwoBasisIso (a : R) :
    (tensorCube (oneKoszulComplex a)).X (-2) ≅
      ModuleCat.of R R ⊞ (ModuleCat.of R R ⊞ ModuleCat.of R R) where
  hom := biprod.lift (oneKoszulCubeE01Coordinate a)
    (biprod.lift (oneKoszulCubeE02Coordinate a) (oneKoszulCubeE12Coordinate a))
  inv := biprod.desc (oneKoszulCubeE01 a)
    (biprod.desc (oneKoszulCubeE02 a) (oneKoszulCubeE12 a))
  hom_inv_id := by
    apply oneKoszulCubeXNegTwo_hom_ext a <;> simp [biprod.lift_desc]
  inv_hom_id := by
    apply biprod.hom_ext
    · apply biprod.hom_ext'
      · simp [Category.assoc]
      · apply biprod.hom_ext'
        · simp [Category.assoc]
        · simp [Category.assoc]
    · apply biprod.hom_ext
      · apply biprod.hom_ext'
        · simp [Category.assoc]
        · apply biprod.hom_ext'
          · simp [Category.assoc]
          · simp [Category.assoc]
      · apply biprod.hom_ext'
        · simp [Category.assoc]
        · apply biprod.hom_ext'
          · simp [Category.assoc]
          · simp [Category.assoc]

/-- Convert the ordered triple product to Fin 3 coordinates. -/
def triplePairLinearEquiv (R : Type u) [CommRing R] : (R × (R × R)) ≃ₗ[R] (Fin 3 → R) where
  toFun x := Fin.cases x.1 (Fin.cases x.2.1 (Fin.cases x.2.2 (fun i => Fin.elim0 i)))
  invFun y := (y 0, (y 1, y 2))
  left_inv _ := rfl
  right_inv y := by funext i; fin_cases i <;> rfl
  map_add' x y := by funext i; fin_cases i <;> rfl
  map_smul' c x := by funext i; fin_cases i <;> rfl

def oneKoszulCubeNegOneVectorIso (a : R) :
    (tensorCube (oneKoszulComplex a)).X (-1) ≅
      ModuleCat.of R (Fin 3 → R) :=
  oneKoszulCubeNegOneBasisIso a ≪≫
    biprod.mapIso (Iso.refl _) (ModuleCat.biprodIsoProd (ModuleCat.of R R) (ModuleCat.of R R)) ≪≫
    ModuleCat.biprodIsoProd (ModuleCat.of R R) (ModuleCat.of R (R × R)) ≪≫
    (triplePairLinearEquiv R).toModuleIso

def oneKoszulCubeNegTwoVectorIso (a : R) :
    (tensorCube (oneKoszulComplex a)).X (-2) ≅
      ModuleCat.of R (Fin 3 → R) :=
  oneKoszulCubeNegTwoBasisIso a ≪≫
    biprod.mapIso (Iso.refl _) (ModuleCat.biprodIsoProd (ModuleCat.of R R) (ModuleCat.of R R)) ≪≫
    ModuleCat.biprodIsoProd (ModuleCat.of R R) (ModuleCat.of R (R × R)) ≪≫
    (triplePairLinearEquiv R).toModuleIso

end Adams
end SerrePositivity
