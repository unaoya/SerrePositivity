module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraHomotopyPullbackMap

/-!
概要：実 cospan の経路模型を、通常の図式圏上の厳密な関手へまとめる。
方針：三成分の一意性と経路関手の恒等・合成則から関手則を証明する。
規約：二脚は元の射を使う。使われ方：像への制限で得る拡大の塔。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits WalkingCospan WalkingCospan.Hom
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.HomotopyPullbackModel
variable (R : Type u) [CommRing R]

def diagramObject (D : WalkingCospan ⥤ Mon (Complex R)) : Mon (Complex R) :=
  algebra R (D.map inl) (D.map inr)

def diagramMap {D E : WalkingCospan ⥤ Mon (Complex R)} (α : D ⟶ E) :
    diagramObject R D ⟶ diagramObject R E :=
  map R (D.map inl) (D.map inr) (E.map inl) (E.map inr)
    (α.app .left) (α.app .one) (α.app .right)
    (α.naturality inl).symm (α.naturality inr).symm

lemma diagramMap_left {D E : WalkingCospan ⥤ Mon (Complex R)} (α : D ⟶ E) :
    diagramMap R α ≫ left R (E.map inl) (E.map inr) =
      left R (D.map inl) (D.map inr) ≫ α.app .left := map_left R _ _ _ _ _ _ _ _ _

lemma diagramMap_right {D E : WalkingCospan ⥤ Mon (Complex R)} (α : D ⟶ E) :
    diagramMap R α ≫ right R (E.map inl) (E.map inr) =
      right R (D.map inl) (D.map inr) ≫ α.app .right := map_right R _ _ _ _ _ _ _ _ _

lemma diagramMap_path {D E : WalkingCospan ⥤ Mon (Complex R)} (α : D ⟶ E) :
    diagramMap R α ≫ path R (E.map inl) (E.map inr) =
      path R (D.map inl) (D.map inr) ≫ Path.map R (α.app .one) :=
  map_path R _ _ _ _ _ _ _ _ _

lemma diagramMap_id (D : WalkingCospan ⥤ Mon (Complex R)) :
    diagramMap R (𝟙 D) = 𝟙 (diagramObject R D) := by
  apply hom_ext R (D.map inl) (D.map inr)
  · rw [diagramMap_left]; simp
  · rw [diagramMap_right]; simp
  · rw [diagramMap_path]; simp [Path.map_id]

lemma diagramMap_comp {D E F : WalkingCospan ⥤ Mon (Complex R)}
    (α : D ⟶ E) (β : E ⟶ F) : diagramMap R (α ≫ β) = diagramMap R α ≫ diagramMap R β := by
  apply hom_ext R (F.map inl) (F.map inr)
  · rw [diagramMap_left, Category.assoc, diagramMap_left, ← Category.assoc, diagramMap_left]
    rfl
  · rw [diagramMap_right, Category.assoc, diagramMap_right, ← Category.assoc, diagramMap_right]
    rfl
  · rw [diagramMap_path, Category.assoc, diagramMap_path, ← Category.assoc, diagramMap_path]
    exact congrArg (fun q ↦ path R (D.map inl) (D.map inr) ≫ q)
      (Path.map_comp R (α.app .one) (β.app .one))

def diagramFunctor : (WalkingCospan ⥤ Mon (Complex R)) ⥤ Mon (Complex R) where
  obj := diagramObject R
  map := diagramMap R
  map_id := diagramMap_id R
  map_comp := diagramMap_comp R

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.HomotopyPullbackModel
