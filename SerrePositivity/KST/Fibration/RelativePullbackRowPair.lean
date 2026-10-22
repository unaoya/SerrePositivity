module
public import SerrePositivity.KST.Fibration.RelativePullbackS

/-! # 相対引き戻しの S_n 行で元の二成分を保つ射対の比較 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.KST.SConstruction
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration

/-- 元の射対の S_n 行と、交換した相対 cofiber の射対は同じ端の同型で厳密に可換。 -/
lemma RelativePullback.sRow_pair {X : StableModel.{u}} {A B : ClosedStablePredicate X}
    (D : RelativePullback X A B) (n : ℕ) (F : StableModel.{u} ⥤ SSet.{u}) :
    D.pair (sEndofunctor n ⋙ F) ≫ (𝟙 _ ⊗ₘ F.map (sClosedStableIso n B).hom) =
      (D.sRow n).pair F := by
  unfold RelativePullback.pair
  rw [lift_map, Category.comp_id, D.sRow_quotient, F.map_comp]
  rfl

/-- 交換した相対引き戻しの比較同値は、元の同じ S_n 行の射対へ戻る。 -/
lemma RelativePullback.rowPair_localized_isIso {X : StableModel.{u}}
    {A B : ClosedStablePredicate X} (D : RelativePullback X A B) (n : ℕ)
    (F : StableModel.{u} ⥤ SSet.{u})
    (h : IsIso (AnodyneHomotopy.anodyneQ.map ((D.sRow n).pair F))) :
    IsIso (AnodyneHomotopy.anodyneQ.map (D.pair (sEndofunctor n ⋙ F))) := by
  have : IsIso (AnodyneHomotopy.anodyneQ.map
      (𝟙 (F.obj (sStableModel n D.base)) ⊗ₘ (F.mapIso (sClosedStableIso n B)).hom)) :=
    inferInstance
  have hi : IsIso (AnodyneHomotopy.anodyneQ.map
      (D.pair (sEndofunctor n ⋙ F) ≫ (𝟙 _ ⊗ₘ F.map (sClosedStableIso n B).hom))) := by
    rw [D.sRow_pair]
    exact h
  rw [Functor.map_comp] at hi
  exact (isIso_comp_right_iff _ _).mp hi

end SerrePositivity.KST.Fibration
