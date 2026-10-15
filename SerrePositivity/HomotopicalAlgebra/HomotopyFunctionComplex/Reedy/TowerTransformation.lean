module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.DiagramGluing

/-! # Natural transformations between coherent degree towers -/

@[expose] public section
universe v u v' u'
noncomputable section
open CategoryTheory HomotopicalAlgebra

namespace SerrePositivity.Reedy.DiagramTower
variable {J : Type u} [Category.{v} J] {inverse direct : MorphismProperty J}
  [inverse.IsMultiplicative] [direct.IsMultiplicative]
  {r : ReedyStructure inverse direct ℕ} {C : Type u'} [Category.{v'} C]

structure Map (T S : DiagramTower r C) where
  app (n : ℕ) : T.stage n ⟶ S.stage n
  step (n : ℕ) : Functor.whiskerLeft (lowerMap r (Nat.le_succ n)) (app (n + 1)) ≫
    (S.step n).hom = (T.step n).hom ≫ app n

namespace Map
variable {T S U : DiagramTower r C} (m : Map T S)

@[reassoc]
lemma comparison {n k : ℕ} (h : n ≤ k) (j : J) (hj : r.deg j < n) :
    (m.app k).app ⟨j, lt_of_lt_of_le hj h⟩ ≫ (S.comparisonAt h j hj).hom =
      (T.comparisonAt h j hj).hom ≫ (m.app n).app ⟨j, hj⟩ := by
  induction k, h using Nat.le_induction with
  | base => simp only [comparisonAt_refl, Iso.refl_hom, Category.id_comp, Category.comp_id]
  | succ k h ih =>
    rw [S.comparisonAt_succ h, T.comparisonAt_succ h]
    simp only [Iso.trans_hom, Category.assoc]
    have hs := congr_app (m.step k) (⟨j, lt_of_lt_of_le hj h⟩ : Lower r k)
    change (m.app (k + 1)).app ⟨j, lt_of_lt_of_le hj (h.trans (Nat.le_succ k))⟩ ≫
        ((S.step k).app (⟨j, lt_of_lt_of_le hj h⟩ : Lower r k)).hom =
      ((T.step k).app (⟨j, lt_of_lt_of_le hj h⟩ : Lower r k)).hom ≫
        (m.app k).app ⟨j, lt_of_lt_of_le hj h⟩ at hs
    rw [← Category.assoc, hs, Category.assoc, ih]

abbrev globalApp (j : J) : T.obj j ⟶ S.obj j :=
  (m.app (r.deg j + 1)).app ⟨j, Nat.lt_succ_self _⟩

lemma globalApp_eq (n : ℕ) (j : J) (hj : r.deg j < n) :
    m.globalApp j = (T.objIso n j hj).inv ≫ (m.app n).app ⟨j, hj⟩ ≫
      (S.objIso n j hj).hom := by
  have h := m.comparison (Nat.succ_le_of_lt hj) j (Nat.lt_succ_self _)
  change (m.app n).app ⟨j, hj⟩ ≫ (S.objIso n j hj).hom =
    (T.objIso n j hj).hom ≫ m.globalApp j at h
  rw [h, Iso.inv_hom_id_assoc]

lemma naturality {j k : J} (f : j ⟶ k) :
    T.map f ≫ m.globalApp k = m.globalApp j ≫ S.map f := by
  let n := max (r.deg j) (r.deg k) + 1
  have hj : r.deg j < n := lt_of_le_of_lt (le_max_left _ _) (Nat.lt_succ_self _)
  have hk : r.deg k < n := lt_of_le_of_lt (le_max_right _ _) (Nat.lt_succ_self _)
  rw [T.map_eq n hj hk, S.map_eq n hj hk, m.globalApp_eq n j hj, m.globalApp_eq n k hk]
  simp only [mapAt, Category.assoc, Iso.hom_inv_id_assoc]
  rw [(m.app n).naturality_assoc (ObjectProperty.homMk f : (⟨j, hj⟩ : Lower r n) ⟶ ⟨k, hk⟩)]

def toNatTrans : T.toFunctor ⟶ S.toFunctor where
  app := m.globalApp
  naturality _ _ f := m.naturality f

variable (T) in
abbrev id : Map T T where
  app n := 𝟙 (T.stage n)
  step n := by ext x; simp

abbrev comp (m' : Map S U) : Map T U where
  app n := m.app n ≫ m'.app n
  step n := by
    ext x
    have h := congr_app (m.step n) x
    have h' := congr_app (m'.step n) x
    change (m.app (n + 1)).app _ ≫ ((S.step n).hom.app x) =
      (T.step n).hom.app x ≫ (m.app n).app x at h
    change (m'.app (n + 1)).app _ ≫ ((U.step n).hom.app x) =
      (S.step n).hom.app x ≫ (m'.app n).app x at h'
    change ((m.app (n + 1)).app _ ≫ (m'.app (n + 1)).app _) ≫ (U.step n).hom.app x =
      (T.step n).hom.app x ≫ ((m.app n).app x ≫ (m'.app n).app x)
    rw [Category.assoc, h', ← Category.assoc, h, Category.assoc]

@[simp]
lemma toNatTrans_id (T : DiagramTower r C) : (id T).toNatTrans = 𝟙 T.toFunctor := rfl

@[simp]
lemma toNatTrans_comp (m' : Map S U) :
    (m.comp m').toNatTrans = m.toNatTrans ≫ m'.toNatTrans := rfl

end Map
end SerrePositivity.Reedy.DiagramTower
