module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.TowerOfFunctor

/-! # Gluing coherent degreewise factorizations

The input contains only diagrams and factorizations on finite degree
restrictions, with their successive compatibility. The output is an actual
factorization on the entire index category and recovers both legs on every
finite restriction.
-/

@[expose] public section
universe v u v' u'
noncomputable section
open CategoryTheory HomotopicalAlgebra

namespace SerrePositivity.Reedy
variable {J : Type u} [Category.{v} J] {inverse direct : MorphismProperty J}
  [inverse.IsMultiplicative] [direct.IsMultiplicative]
  (r : ReedyStructure inverse direct ℕ) {C : Type u'} [Category.{v'} C]
  {F G : J ⥤ C} (τ : F ⟶ G)

structure FactorizationTower where
  diagram : DiagramTower r C
  left : DiagramTower.Map (DiagramTower.ofFunctor r F) diagram
  right : DiagramTower.Map diagram (DiagramTower.ofFunctor r G)
  fac (n : ℕ) : left.app n ≫ right.app n = Functor.whiskerLeft (lowerInclusion r n) τ

namespace FactorizationTower
variable {r τ} (K : FactorizationTower r τ)

abbrev leftMap : F ⟶ K.diagram.toFunctor :=
  (DiagramTower.ofFunctorIso r F).inv ≫ K.left.toNatTrans

abbrev rightMap : K.diagram.toFunctor ⟶ G :=
  K.right.toNatTrans ≫ (DiagramTower.ofFunctorIso r G).hom

lemma leftMap_rightMap : K.leftMap ≫ K.rightMap = τ := by
  ext j
  change (𝟙 _ ≫ (K.left.app (r.deg j + 1)).app ⟨j, Nat.lt_succ_self _⟩) ≫
    ((K.right.app (r.deg j + 1)).app ⟨j, Nat.lt_succ_self _⟩ ≫ 𝟙 _) = τ.app j
  rw [Category.id_comp, Category.comp_id]
  exact congr_app (K.fac (r.deg j + 1)) ⟨j, Nat.lt_succ_self _⟩

abbrev factorizationData : MorphismProperty.MapFactorizationData ⊤ ⊤ τ where
  Z := K.diagram.toFunctor
  i := K.leftMap
  p := K.rightMap
  fac := K.leftMap_rightMap
  hi := trivial
  hp := trivial

lemma leftMap_restriction (n : ℕ) :
    Functor.whiskerLeft (lowerInclusion r n) K.leftMap =
      K.left.app n ≫ (K.diagram.restrictionIso n).hom := by
  ext x
  change 𝟙 _ ≫ K.left.globalApp x.obj =
    (K.left.app n).app x ≫ (K.diagram.objIso n x.obj x.property).hom
  rw [Category.id_comp, K.left.globalApp_eq n x.obj x.property]
  change ((DiagramTower.ofFunctor r F).comparisonAt _ x.obj _).inv ≫
    (K.left.app n).app x ≫ (K.diagram.objIso n x.obj x.property).hom = _
  rw [DiagramTower.ofFunctor_comparisonAt]
  exact Category.id_comp _

lemma rightMap_restriction (n : ℕ) :
    (K.diagram.restrictionIso n).hom ≫ Functor.whiskerLeft (lowerInclusion r n) K.rightMap =
      K.right.app n := by
  ext x
  change (K.diagram.objIso n x.obj x.property).hom ≫ (K.right.globalApp x.obj ≫ 𝟙 _) = _
  rw [Category.comp_id, K.right.globalApp_eq n x.obj x.property]
  change (K.diagram.objIso n x.obj x.property).hom ≫
    ((K.diagram.objIso n x.obj x.property).inv ≫ (K.right.app n).app x ≫
      ((DiagramTower.ofFunctor r G).comparisonAt _ x.obj _).hom) = _
  rw [DiagramTower.ofFunctor_comparisonAt]
  simp only [Iso.refl_hom, Iso.hom_inv_id_assoc]
  exact Category.comp_id ((K.right.app n).app x)

end FactorizationTower
end SerrePositivity.Reedy
