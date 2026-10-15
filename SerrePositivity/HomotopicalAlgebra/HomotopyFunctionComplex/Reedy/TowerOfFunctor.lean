module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.TowerTransformation

/-! # The restriction tower of an actual functor and its reconstruction -/

@[expose] public section
universe v u v' u'
noncomputable section
open CategoryTheory HomotopicalAlgebra

namespace SerrePositivity.Reedy.DiagramTower
variable {J : Type u} [Category.{v} J] {inverse direct : MorphismProperty J}
  [inverse.IsMultiplicative] [direct.IsMultiplicative]
  (r : ReedyStructure inverse direct ℕ) {C : Type u'} [Category.{v'} C]

abbrev ofFunctor (F : J ⥤ C) : DiagramTower r C where
  stage n := lowerInclusion r n ⋙ F
  step _ := Iso.refl _

lemma ofFunctor_comparisonAt (F : J ⥤ C) {n m : ℕ} (h : n ≤ m)
    (j : J) (hj : r.deg j < n) :
    (ofFunctor r F).comparisonAt h j hj = Iso.refl (F.obj j) := by
  induction m, h using Nat.le_induction with
  | base => rw [comparisonAt_refl]; rfl
  | succ m h ih =>
    rw [(ofFunctor r F).comparisonAt_succ h, ih]
    change Iso.refl (F.obj j) ≪≫ Iso.refl (F.obj j) = Iso.refl (F.obj j)
    exact Iso.refl_trans _

lemma ofFunctor_toFunctor_map (F : J ⥤ C) {j k : J} (f : j ⟶ k) :
    (ofFunctor r F).toFunctor.map f = F.map f := by
  let n := max (r.deg j) (r.deg k) + 1
  have hj : r.deg j < n := lt_of_le_of_lt (le_max_left _ _) (Nat.lt_succ_self _)
  have hk : r.deg k < n := lt_of_le_of_lt (le_max_right _ _) (Nat.lt_succ_self _)
  change (ofFunctor r F).map f = _
  rw [map_eq _ n hj hk]
  change ((ofFunctor r F).comparisonAt _ j _).inv ≫ F.map f ≫
    ((ofFunctor r F).comparisonAt _ k _).hom = _
  rw [ofFunctor_comparisonAt, ofFunctor_comparisonAt]
  change 𝟙 (F.obj j) ≫ F.map f ≫ 𝟙 (F.obj k) = F.map f
  rw [Category.id_comp, Category.comp_id]

def ofFunctorIso (F : J ⥤ C) : (ofFunctor r F).toFunctor ≅ F :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun {x y} f ↦ by
    change (ofFunctor r F).toFunctor.map f ≫ 𝟙 (F.obj y) = 𝟙 (F.obj x) ≫ F.map f
    rw [ofFunctor_toFunctor_map]
    change F.map f ≫ 𝟙 (F.obj y) = 𝟙 (F.obj x) ≫ F.map f
    rw [Category.id_comp, Category.comp_id])

abbrev ofNatTrans {F G : J ⥤ C} (τ : F ⟶ G) : Map (ofFunctor r F) (ofFunctor r G) where
  app n := Functor.whiskerLeft (lowerInclusion r n) τ
  step n := by
    ext x
    change τ.app x.obj ≫ 𝟙 _ = 𝟙 _ ≫ τ.app x.obj
    rw [Category.id_comp, Category.comp_id]

lemma ofFunctorIso_naturality {F G : J ⥤ C} (τ : F ⟶ G) :
    (ofNatTrans r τ).toNatTrans ≫ (ofFunctorIso r G).hom = (ofFunctorIso r F).hom ≫ τ := by
  ext x
  change τ.app x ≫ 𝟙 _ = 𝟙 _ ≫ τ.app x
  rw [Category.id_comp, Category.comp_id]

end SerrePositivity.Reedy.DiagramTower
