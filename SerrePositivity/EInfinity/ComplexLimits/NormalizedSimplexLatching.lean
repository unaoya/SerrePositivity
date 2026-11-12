module

public import SerrePositivity.EInfinity.ComplexLimits.NormalizedSimplexReedy
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedSimplexTensorHom

/-!
# 正規化単体の実 latching 矢と元の境界包含

概要：実 latching 矢を同じ正規化境界の矢へ同定する。
方針：小さい余極限の保存と標準境界の実比較同型を合成する。
規約：始域だけでなく指定した矢全体を比較する。
使われ方：任意 X をテンソルした frame の cofibrancy の判定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory Limits MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.Reedy
variable (A : Type u) [CommRing A]

def normalizedSimplexLatchingArrowIso (n : ℕ) :
    Arrow.mk ((latchingComparison simplex (SimplexCategory.mk n)).app
      (SSet.stdSimplex ⋙ BarrattEccles.normalizedFunctor A)) ≅
        Arrow.mk ((BarrattEccles.normalizedFunctor A).map (SSet.boundary.{0} n).ι) := by
  have := normalizedFunctor_preservesSmallColimits A
  refine latchingComparison_preservedIso simplex (BarrattEccles.normalizedFunctor A)
    SSet.stdSimplex (SimplexCategory.mk n) ≪≫ ?_
  refine Arrow.isoMk ((BarrattEccles.normalizedFunctor A).mapIso
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72.standardBoundaryIso.{0} n)) (Iso.refl _) ?_
  change (BarrattEccles.normalizedFunctor A).map _ ≫
    (BarrattEccles.normalizedFunctor A).map _ =
      (BarrattEccles.normalizedFunctor A).map _ ≫ 𝟙 _
  rw [Category.comp_id, ← Functor.map_comp, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72.standardBoundaryIso_fac]

def normalizedSimplexTensorLatchingArrowIso (X : Complex A) (n : ℕ) :
    Arrow.mk ((latchingComparison simplex (SimplexCategory.mk n)).app
      (normalizedSimplexTensor A X)) ≅
        Arrow.mk (X ◁ (BarrattEccles.normalizedFunctor A).map (SSet.boundary.{0} n).ι) :=
  latchingComparison_preservedIso simplex (tensorLeft X)
    (SSet.stdSimplex ⋙ BarrattEccles.normalizedFunctor A) (SimplexCategory.mk n) ≪≫
      (tensorLeft X).mapArrow.mapIso (normalizedSimplexLatchingArrowIso A n)

end SerrePositivity.EInfinity.ComplexLimits
