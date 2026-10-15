module

public import SerrePositivity.HomotopicalAlgebra.Diagram.ContinuousLiftSystem

/-! # Extending coherent lifts across a successor stage -/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.DiagramModel.ContinuousLifts
variable {J : Type w} [LinearOrder J] [SuccOrder J] {C : Type u} [Category.{v} C]
  {D U V : J ⥤ C} {p : U ⟶ V} {b : D ⟶ V} {j : J}

namespace Partial

def succHom (x : Partial p b j) (l : D.obj (Order.succ j) ⟶ U.obj (Order.succ j))
    (i : J) (hi : i ≤ Order.succ j) : D.obj i ⟶ U.obj i := by
  classical
  by_cases h : i ≤ j
  · exact x.hom i h
  · have he : i = Order.succ j := le_antisymm hi
      (Order.succ_le_of_lt (lt_of_not_ge h))
    exact eqToHom (congrArg D.obj he) ≫ l ≫ eqToHom (congrArg U.obj he.symm)

lemma succHom_of_le (x : Partial p b j) (l : D.obj (Order.succ j) ⟶ U.obj (Order.succ j))
    (i : J) (hi : i ≤ Order.succ j) (h : i ≤ j) : succHom x l i hi = x.hom i h := by
  simp only [succHom, dite_eq_left h]

lemma succHom_top (x : Partial p b j) (hj : ¬IsMax j)
    (l : D.obj (Order.succ j) ⟶ U.obj (Order.succ j)) (h : Order.succ j ≤ Order.succ j) :
    succHom x l (Order.succ j) h = l := by
  simp [succHom, not_le_of_gt (Order.lt_succ_of_not_isMax hj)]

def extendSucc (x : Partial p b j) (hj : ¬IsMax j)
    (l : D.obj (Order.succ j) ⟶ U.obj (Order.succ j))
    (hl : D.map (homOfLE (Order.le_succ j)) ≫ l =
      x.hom j le_rfl ≫ U.map (homOfLE (Order.le_succ j)))
    (hp : l ≫ p.app (Order.succ j) = b.app (Order.succ j)) : Partial p b (Order.succ j) where
  hom := succHom x l
  naturality {i k} hik hk := by
    by_cases hk₀ : k ≤ j
    · rw [succHom_of_le x l k hk hk₀, succHom_of_le x l i _ (hik.trans hk₀)]
      exact x.naturality hik hk₀
    · have hk₁ : k = Order.succ j := le_antisymm hk (Order.succ_le_of_lt (lt_of_not_ge hk₀))
      subst k
      by_cases hi₀ : i ≤ j
      · rw [succHom_top x hj l, succHom_of_le x l i _ hi₀]
        calc
          D.map (homOfLE hik) ≫ l =
              (D.map (homOfLE hi₀) ≫ D.map (homOfLE (Order.le_succ j))) ≫ l := by
            rw [← D.map_comp]
            rfl
          _ = D.map (homOfLE hi₀) ≫
              (x.hom j le_rfl ≫ U.map (homOfLE (Order.le_succ j))) := by rw [Category.assoc, hl]
          _ = (x.hom i hi₀ ≫ U.map (homOfLE hi₀)) ≫ U.map (homOfLE (Order.le_succ j)) := by
            rw [← Category.assoc, x.naturality hi₀ le_rfl]
          _ = x.hom i hi₀ ≫ U.map (homOfLE hik) := by
            rw [Category.assoc, ← U.map_comp]
            rfl
      · have hi₁ : i = Order.succ j := le_antisymm hik
          (Order.succ_le_of_lt (lt_of_not_ge hi₀))
        subst i
        simp only [homOfLE_refl, D.map_id, U.map_id, Category.id_comp, Category.comp_id]
  fac i hi := by
    by_cases hi₀ : i ≤ j
    · rw [succHom_of_le x l i hi hi₀]
      exact x.fac i hi₀
    · have hi₁ : i = Order.succ j := le_antisymm hi
        (Order.succ_le_of_lt (lt_of_not_ge hi₀))
      subst i
      rw [succHom_top x hj l]
      exact hp

lemma restrict_extendSucc (x : Partial p b j) (hj : ¬IsMax j)
    (l : D.obj (Order.succ j) ⟶ U.obj (Order.succ j))
    (hl : D.map (homOfLE (Order.le_succ j)) ≫ l =
      x.hom j le_rfl ≫ U.map (homOfLE (Order.le_succ j)))
    (hp : l ≫ p.app (Order.succ j) = b.app (Order.succ j)) :
    (extendSucc x hj l hl hp).restrict (Order.le_succ j) = x := by
  apply Partial.ext
  funext i hi
  exact succHom_of_le x l i (hi.trans (Order.le_succ j)) hi

end Partial
end SerrePositivity.DiagramModel.ContinuousLifts
