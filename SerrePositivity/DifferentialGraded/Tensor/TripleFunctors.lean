module
public import SerrePositivity.DifferentialGraded.Tensor.BimoduleFunctor

/-! # 三つの閉零bimoduleの反復合成関手 -/
@[expose] public section
noncomputable section
universe u v w z t
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z) (F : Type t)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F]
  [Small.{u} B] [Small.{u} C] [Small.{u} E]

/-- 左括弧付けの実際の三変数合成関手。 -/
def leftTripleFunctor :
    (BimoduleCategory A B C × BimoduleCategory A C E) × BimoduleCategory A E F ⥤
      BimoduleCategory A B F :=
  ((composeFunctor A B C E).prod (𝟭 (BimoduleCategory A E F))) ⋙ composeFunctor A B E F

/-- 右括弧付けの実際の三変数合成関手。 -/
def rightTripleFunctor :
    (BimoduleCategory A B C × BimoduleCategory A C E) × BimoduleCategory A E F ⥤
      BimoduleCategory A B F where
  obj X := BimoduleCategory.of A B F
    (compose A B C F (BimoduleCategory.underlying A B C X.1.1)
      (compose A C E F (BimoduleCategory.underlying A C E X.1.2)
        (BimoduleCategory.underlying A E F X.2)))
  map f := composeMap A B C F f.1.1 (composeMap A C E F f.1.2 f.2)
  map_id X := by
    change composeMap A B C F (𝟙 X.1.1) (composeMap A C E F (𝟙 X.1.2) (𝟙 X.2)) = _
    rw [composeMap_id]
    exact composeMap_id A B C F _ _
  map_comp f g := by
    change composeMap A B C F (f.1.1 ≫ g.1.1)
      (composeMap A C E F (f.1.2 ≫ g.1.2) (f.2 ≫ g.2)) = _
    rw [composeMap_comp]
    exact composeMap_comp A B C F _ _ _ _

end SerrePositivity.DifferentialGraded.BimoduleTensor
