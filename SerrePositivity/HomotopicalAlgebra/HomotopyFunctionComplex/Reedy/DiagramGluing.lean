module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.DiagramTower

/-! # Gluing coherent degree-restricted diagrams to an actual functor -/

@[expose] public section
universe v u v' u'
noncomputable section
open CategoryTheory HomotopicalAlgebra

namespace SerrePositivity.Reedy.DiagramTower
variable {J : Type u} [Category.{v} J] {inverse direct : MorphismProperty J}
  [inverse.IsMultiplicative] [direct.IsMultiplicative]
  {r : ReedyStructure inverse direct ℕ} {C : Type u'} [Category.{v'} C]
  (T : DiagramTower r C)

abbrev obj (j : J) : C := (T.stage (r.deg j + 1)).obj ⟨j, Nat.lt_succ_self _⟩

abbrev objIso (n : ℕ) (j : J) (hj : r.deg j < n) :
    (T.stage n).obj ⟨j, hj⟩ ≅ T.obj j :=
  T.comparisonAt (Nat.succ_le_of_lt hj) j (Nat.lt_succ_self _)

lemma objIso_mono {n m : ℕ} (h : n ≤ m) (j : J) (hj : r.deg j < n) :
    T.objIso m j (lt_of_lt_of_le hj h) = T.comparisonAt h j hj ≪≫ T.objIso n j hj :=
  T.comparisonAt_trans (Nat.succ_le_of_lt hj) h j (Nat.lt_succ_self _)

abbrev mapAt (n : ℕ) {j k : J} (hj : r.deg j < n) (hk : r.deg k < n)
    (f : j ⟶ k) : T.obj j ⟶ T.obj k :=
  (T.objIso n j hj).inv ≫ (T.stage n).map (ObjectProperty.homMk f) ≫
    (T.objIso n k hk).hom

lemma mapAt_mono {n m : ℕ} (h : n ≤ m) {j k : J}
    (hj : r.deg j < n) (hk : r.deg k < n) (f : j ⟶ k) :
    T.mapAt m (lt_of_lt_of_le hj h) (lt_of_lt_of_le hk h) f = T.mapAt n hj hk f := by
  unfold mapAt
  rw [T.objIso_mono h j hj, T.objIso_mono h k hk]
  simp only [Iso.trans_inv, Iso.trans_hom, Category.assoc]
  rw [T.comparisonAt_naturality_assoc h hj hk f]
  simp only [Iso.inv_hom_id_assoc]

abbrev map {j k : J} (f : j ⟶ k) : T.obj j ⟶ T.obj k :=
  T.mapAt (max (r.deg j) (r.deg k) + 1)
    (lt_of_le_of_lt (le_max_left _ _) (Nat.lt_succ_self _))
    (lt_of_le_of_lt (le_max_right _ _) (Nat.lt_succ_self _)) f

lemma map_eq (n : ℕ) {j k : J} (hj : r.deg j < n) (hk : r.deg k < n) (f : j ⟶ k) :
    T.map f = T.mapAt n hj hk f :=
  (T.mapAt_mono (Nat.succ_le_of_lt (max_lt hj hk)) _ _ f).symm

lemma map_id (j : J) : T.map (𝟙 j) = 𝟙 (T.obj j) := by
  rw [T.map_eq (r.deg j + 1) (Nat.lt_succ_self _) (Nat.lt_succ_self _)]
  change (T.objIso _ j _).inv ≫ (T.stage _).map (𝟙 _) ≫ (T.objIso _ j _).hom = _
  rw [Functor.map_id, Category.id_comp, Iso.inv_hom_id]

lemma map_comp {i j k : J} (f : i ⟶ j) (g : j ⟶ k) :
    T.map (f ≫ g) = T.map f ≫ T.map g := by
  let n := max (r.deg i) (max (r.deg j) (r.deg k)) + 1
  have hi : r.deg i < n := lt_of_le_of_lt (le_max_left _ _) (Nat.lt_succ_self _)
  have hj : r.deg j < n := lt_of_le_of_lt
    ((le_max_left _ _).trans (le_max_right _ _)) (Nat.lt_succ_self _)
  have hk : r.deg k < n := lt_of_le_of_lt
    ((le_max_right _ _).trans (le_max_right _ _)) (Nat.lt_succ_self _)
  rw [T.map_eq n hi hk, T.map_eq n hi hj, T.map_eq n hj hk]
  change (T.objIso n i hi).inv ≫
      (T.stage n).map ((ObjectProperty.homMk f : ⟨i, hi⟩ ⟶ ⟨j, hj⟩) ≫
        (ObjectProperty.homMk g : ⟨j, hj⟩ ⟶ ⟨k, hk⟩)) ≫ (T.objIso n k hk).hom = _
  rw [Functor.map_comp]
  simp only [mapAt, Category.assoc, Iso.hom_inv_id_assoc]

def toFunctor : J ⥤ C where
  obj := T.obj
  map := T.map
  map_id := T.map_id
  map_comp := T.map_comp

/-- Every prescribed finite restriction is recovered by a natural isomorphism. -/
def restrictionIso (n : ℕ) : T.stage n ≅ lowerInclusion r n ⋙ T.toFunctor :=
  NatIso.ofComponents (fun x ↦ T.objIso n x.obj x.property) (fun {x y} f ↦ by
    change (T.stage n).map f ≫ (T.objIso n y.obj y.property).hom =
      (T.objIso n x.obj x.property).hom ≫ T.map f.hom
    rw [T.map_eq n x.property y.property]
    simp only [mapAt, Iso.hom_inv_id_assoc]
    rfl)

end SerrePositivity.Reedy.DiagramTower
