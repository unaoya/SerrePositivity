module
public import SerrePositivity.InfinityCategories.F1.Transport.LocalizedPairEquality

/-! # anodyne 局所化での元の Cartesian 射対の二成分の比較 -/

@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration

/-- 局所化射の等号は、任意の固定対象との右直積でも保たれる。 -/
lemma whiskerRight_eq_of_anodyneQ_eq {X Y : SSet.{u}} {f g : X ⟶ Y}
    (h : AnodyneHomotopy.anodyneQ.map f = AnodyneHomotopy.anodyneQ.map g)
    (A : SSet.{u}) :
    AnodyneHomotopy.anodyneQ.map (f ▷ A) = AnodyneHomotopy.anodyneQ.map (g ▷ A) := by
  apply map_eq_of_anodyneQ_eq (tensorRight A ⋙ AnodyneHomotopy.anodyneQ) _ h
  intro U V i hi
  exact Localization.inverts AnodyneHomotopy.anodyneQ SSet.anodyneExtensions _
    (hi.whiskerRight A)

/-- 元の第二成分を固定した射対は、第一成分の局所化等号を保つ。 -/
lemma pair_left_eq_of_anodyneQ_eq {X Y Z : SSet.{u}} {f g : X ⟶ Y} (k : X ⟶ Z)
    (h : AnodyneHomotopy.anodyneQ.map f = AnodyneHomotopy.anodyneQ.map g) :
    AnodyneHomotopy.anodyneQ.map (lift f k) = AnodyneHomotopy.anodyneQ.map (lift g k) := by
  have hf : lift (𝟙 X) k ≫ (f ▷ Z) = lift f k := by
    rw [lift_whiskerRight, Category.id_comp]
  have hg : lift (𝟙 X) k ≫ (g ▷ Z) = lift g k := by
    rw [lift_whiskerRight, Category.id_comp]
  rw [← hf, ← hg, Functor.map_comp, Functor.map_comp, whiskerRight_eq_of_anodyneQ_eq h Z]

/-- 元の Cartesian 射対の両成分の局所化等号は、射対全体の局所化等号を与える。 -/
lemma pair_eq_of_anodyneQ_eq {X Y Z : SSet.{u}} {f f' : X ⟶ Y} {g g' : X ⟶ Z}
    (hf : AnodyneHomotopy.anodyneQ.map f = AnodyneHomotopy.anodyneQ.map f')
    (hg : AnodyneHomotopy.anodyneQ.map g = AnodyneHomotopy.anodyneQ.map g') :
    AnodyneHomotopy.anodyneQ.map (lift f g) = AnodyneHomotopy.anodyneQ.map (lift f' g') :=
  (pair_left_eq_of_anodyneQ_eq g hf).trans (pair_right_eq_of_anodyneQ_eq f' hg)

end SerrePositivity.KST.Fibration
