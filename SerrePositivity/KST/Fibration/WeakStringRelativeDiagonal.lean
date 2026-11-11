module
public import SerrePositivity.KST.Fibration.WeakStringObjectRelativeIso

/-! # 元の object S(W 列) と相対 S 構成の対角の厳密同型 -/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Fibration

/-- 二つの単体方向を交換しても、元の対角は自然な厳密同型で一致する。 -/
def simplicialDiagonalFlipIso (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    simplicialDiagonalFunctor.obj X.flip ≅ simplicialDiagonalFunctor.obj X :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro n m θ
    change (X.obj n).map θ ≫ (X.map θ).app m ≫ 𝟙 _ =
      𝟙 _ ≫ (X.map θ).app n ≫ (X.obj m).map θ
    simp only [Category.comp_id, Category.id_comp]
    exact (X.map θ).naturality θ)

/-- 全面・全退化を保つ交換同型から、元の相対 S の対角を直接回収する。 -/
def weakStringObjectRelativeDiagonalIso {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    simplicialDiagonalFunctor.obj
      (weakStringStableSimplicial q ⋙ objectSConstructionFunctor) ≅
        simplicialDiagonalFunctor.obj (relativeSimplicialSConstruction q.hom) :=
  simplicialDiagonalFunctor.mapIso (weakStringObjectRelativeIso q) ≪≫
    simplicialDiagonalFlipIso (relativeSimplicialSConstruction q.hom)

end SerrePositivity.KST.Fibration
