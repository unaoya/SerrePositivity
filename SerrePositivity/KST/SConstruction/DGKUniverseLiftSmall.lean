module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLiftFunctor

/-! # 対象宇宙の持ち上げと元の Small 性
概要：対象ラベルの宇宙を上げても、元の対象の小ささは変わらない。
方針：持ち上げたラベルへの単射で Small 性を移す。
規約：公開名を保持して固定 K 界面への依存を分離。使われ方：入力 Hom end の閉同型。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

/-- 元の対象の小ささは、対象ラベルの宇宙持ち上げ後も保持される。 -/
instance dgKUniverseLift_small : Small.{u} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{v, w} D) := by
  apply small_of_injective (f := fun x : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{v, w} D => x.label)
  intro x y h
  cases x
  cases y
  cases h
  rfl

end SerrePositivity.KST.SConstruction
