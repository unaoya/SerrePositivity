module
public import SerrePositivity.KST.Fibration.WeakStringConstantNaturality
public import SerrePositivity.KST.Fibration.WeakStringRelativeDiagonal

/-! # 元の全定数 W 列の実現と、その対角への同じ定数包含 -/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Fibration

/-- 元の安定入力の任意の実現関手に対する、全列次数の同じ定数包含。 -/
def weakStringRealizationConstant (F : StableModel.{u} ⥤ SSet.{u})
    {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    (Functor.const SimplexCategoryᵒᵖ).obj (F.obj (sInputModel B)) ⟶
      weakStringStableSimplicial q ⋙ F where
  app n := F.map (weakStringConstantExact q n.unop)
  naturality {n m} θ := by
    change 𝟙 _ ≫ F.map (weakStringConstantExact q m.unop) =
      F.map (weakStringConstantExact q n.unop) ≫ F.map (weakStringExactMap q θ.unop)
    rw [Category.id_comp, ← F.map_comp, weakStringConstantExact_reindex]

/-- 元の単体集合の定数な単体的図式の対角を、元の単体集合へ戻す厳密同型。 -/
def constantSSetDiagonalIso (X : SSet.{u}) :
    simplicialDiagonalFunctor.obj ((Functor.const SimplexCategoryᵒᵖ).obj X) ≅ X :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

/-- 元の入力の実現から、全定数 W 列の同じ実現の対角への実際の包含射。 -/
def weakStringRealizationConstantDiagonal (F : StableModel.{u} ⥤ SSet.{u})
    {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    F.obj (sInputModel B) ⟶ simplicialDiagonalFunctor.obj (weakStringStableSimplicial q ⋙ F) :=
  (constantSSetDiagonalIso (F.obj (sInputModel B))).inv ≫
    simplicialDiagonalFunctor.map (weakStringRealizationConstant F q)

end SerrePositivity.KST.Fibration
