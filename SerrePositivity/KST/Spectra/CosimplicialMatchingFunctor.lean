module

public import SerrePositivity.KST.Spectra.CosimplicialHornFactorization
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-!
概要：極限を保つ関手と余単体 matching 射の交換を arrow 同型で表す。
方針：matching 対象の極限保存同型を使い、各射影で matching 比較の式を確認する。
規約：通常の圏の極限保存だけを使い、モデル圏の仮定を課さない。
使われ方：Goerss–Jardine VII §4。点つき loop の Reedy fibrancy 保存。
-/

@[expose] public section
universe u v w z
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.Reedy
namespace SerrePositivity.KST.Spectra.CosimplicialMatchingFunctor
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {C : Type u} [Category.{v} C] [HasLimits C]
  {D : Type w} [Category.{z} D] [HasLimits D]
  (F : C ⥤ D)

/-- 関手で写した matching 射と、関手を施した図式の matching 射の厳密な同型。 -/
def arrowIso (X : CosimplicialObject C) (j : SimplexCategory)
    [PreservesLimit (matchingTarget simplex j ⋙ X) F] :
    Arrow.mk (F.map ((matchingComparison simplex j).app X)) ≅
      Arrow.mk ((matchingComparison simplex j).app (X ⋙ F)) :=
  Arrow.isoMk (Iso.refl _)
    (preservesLimitIso F (matchingTarget simplex j ⋙ X)) (by
      change 𝟙 _ ≫ (matchingComparison simplex j).app (X ⋙ F) =
        F.map ((matchingComparison simplex j).app X) ≫
          (preservesLimitIso F (matchingTarget simplex j ⋙ X)).hom
      rw [Category.id_comp]
      apply limit.hom_ext
      intro a
      rw [Category.assoc]
      erw [preservesLimitIso_hom_π F (matchingTarget simplex j ⋙ X) a]
      rw [← F.map_comp]
      change limit.lift _ (matchingCone simplex (X ⋙ F) j) ≫ limit.π _ a =
        F.map (limit.lift _ (matchingCone simplex X j) ≫ limit.π _ a)
      rw [limit.lift_π, limit.lift_π]
      rfl)

end
end SerrePositivity.KST.Spectra.CosimplicialMatchingFunctor
