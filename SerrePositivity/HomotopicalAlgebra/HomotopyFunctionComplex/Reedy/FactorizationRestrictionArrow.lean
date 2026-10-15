module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.FactorizationTower
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.Subcategory

/-! # Arrow isomorphisms between tower stages and the global factorization -/

@[expose] public section
universe v u v' u'
noncomputable section
open CategoryTheory HomotopicalAlgebra

namespace SerrePositivity.Reedy
variable {J : Type u} [Category.{v} J] {inverse direct : MorphismProperty J}
  [inverse.IsMultiplicative] [direct.IsMultiplicative]
  (r : ReedyStructure inverse direct ℕ) {C : Type u'} [Category.{v'} C]

abbrev upperToLowerSucc (n : ℕ) : Upper r n ⥤ Lower r (n + 1) :=
  ObjectProperty.ιOfLE (fun _ h ↦ Nat.lt_succ_of_le h)

namespace FactorizationTower
variable {r} {F G : J ⥤ C} {τ : F ⟶ G} (K : FactorizationTower r τ) (n : ℕ)

def leftStageArrowIso :
    Arrow.mk (Functor.whiskerLeft (upperToLowerSucc r n) (K.left.app (n + 1))) ≅
      Arrow.mk (Functor.whiskerLeft (upperInclusion r n) K.leftMap) := by
  refine Arrow.isoMk (Iso.refl _)
    (Functor.isoWhiskerLeft (upperToLowerSucc r n) (K.diagram.restrictionIso (n + 1))) ?_
  change 𝟙 (upperInclusion r n ⋙ F) ≫
      Functor.whiskerLeft (upperInclusion r n) K.leftMap =
    Functor.whiskerLeft (upperToLowerSucc r n) (K.left.app (n + 1)) ≫
      (Functor.isoWhiskerLeft (upperToLowerSucc r n) (K.diagram.restrictionIso (n + 1))).hom
  rw [Category.id_comp]
  ext x
  exact congr_app (K.leftMap_restriction (n + 1)) ((upperToLowerSucc r n).obj x)

def rightStageArrowIso :
    Arrow.mk (Functor.whiskerLeft (upperToLowerSucc r n) (K.right.app (n + 1))) ≅
      Arrow.mk (Functor.whiskerLeft (upperInclusion r n) K.rightMap) := by
  refine Arrow.isoMk
    (Functor.isoWhiskerLeft (upperToLowerSucc r n) (K.diagram.restrictionIso (n + 1)))
    (Iso.refl _) ?_
  change (Functor.isoWhiskerLeft (upperToLowerSucc r n) (K.diagram.restrictionIso (n + 1))).hom ≫
      Functor.whiskerLeft (upperInclusion r n) K.rightMap =
    Functor.whiskerLeft (upperToLowerSucc r n) (K.right.app (n + 1)) ≫
      𝟙 (upperInclusion r n ⋙ G)
  ext x
  exact (congr_app (K.rightMap_restriction (n + 1)) ((upperToLowerSucc r n).obj x)).trans
    (Category.comp_id _).symm

end FactorizationTower
end SerrePositivity.Reedy
