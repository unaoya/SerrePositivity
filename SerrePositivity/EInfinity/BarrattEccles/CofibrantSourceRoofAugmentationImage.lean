module

public import SerrePositivity.EInfinity.BarrattEccles.CofibrantSourceRoofNativeRoofComparison
public import SerrePositivity.EInfinity.BarrattEccles.CofibrantHammockInclusionLaws
public import SerrePositivity.EInfinity.BarrattEccles.SourceFrameRoofComparison

/-!
# 元の comma augmentation roof の全代数の source frame 比較への像

概要：元の cofibrant roof 全図式を包含で送ると、保存済み source frame の同じ二列になる。
方針：同じ元の代数射を全頂点・全縦射で照合し、元の余極限と縮約へ移す。
規約：全単体・元の包含・元の比較射を保つ。
使われ方：基準射側 hR の native roof と既存の実基準射の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Limits Opposite SSet _root_.HomotopicalAlgebra
open _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock SerrePositivity.Reedy
open scoped Simplicial
variable (A : Type u) [CommRing A] (X Y : CofibrantAlgebra A)

def cofibrantAlgebraHammockColimitInclusionMap :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph (cofibrantAlgebraRelativeCategory A).weakEquivalences
      (show (cofibrantAlgebraRelativeCategory A).category from X)
      (show (cofibrantAlgebraRelativeCategory A).category from Y) ⟶
    algebraReducedHammock A X.obj Y.obj :=
  (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.reducedColimitIso (cofibrantAlgebraRelativeCategory A).weakEquivalences
    (show (cofibrantAlgebraRelativeCategory A).category from X)
    (show (cofibrantAlgebraRelativeCategory A).category from Y)).hom ≫
      cofibrantAlgebraHammockInclusionMap A _ _

lemma cofibrantAlgebraHammockColimitInclusionMap_graph (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion (cofibrantAlgebraRelativeCategory A).weakEquivalences
      (show (cofibrantAlgebraRelativeCategory A).category from X)
      (show (cofibrantAlgebraRelativeCategory A).category from Y) w ≫
      cofibrantAlgebraHammockColimitInclusionMap A X Y =
    cofibrantAlgebraHammockGraphInclusionMap A
      (show (cofibrantAlgebraRelativeCategory A).category from X)
      (show (cofibrantAlgebraRelativeCategory A).category from Y) w ≫
      algebraHammockGraphInclusion A w X.obj Y.obj ≫
        (algebraHammockReductionIso A X.obj Y.obj).hom := by
  let := modelCategory A
  change _ ≫ ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.reducedColimitIso _ _ _).hom ≫ cofibrantAlgebraHammockInclusionMap A _ _) = _
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.reducedColimitIso_hom_fac]
  have h := cofibrantAlgebraHammockInclusionMap_normalization A
    (show (cofibrantAlgebraRelativeCategory A).category from X)
    (show (cofibrantAlgebraRelativeCategory A).category from Y) w
  exact h.trans (congrArg (fun g => cofibrantAlgebraHammockGraphInclusionMap A
    (show (cofibrantAlgebraRelativeCategory A).category from X)
    (show (cofibrantAlgebraRelativeCategory A).category from Y) w ≫ g)
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.reducedColimitIso_hom_fac (weakEquivalences (operad A).Algebra) X.obj Y.obj w).symm)

variable (b : (cofibrantSourceRoofTarget A X Y) _⦋0⦌)

lemma cofibrantSourceRoofProductCommaAugmentationRoofGraphMap_image :
    cofibrantSourceRoofProductCommaAugmentationRoofGraphMap A X Y b ≫
      cofibrantAlgebraHammockGraphInclusionMap A
        (show (cofibrantAlgebraRelativeCategory A).category from X)
        (show (cofibrantAlgebraRelativeCategory A).category from Y) _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.word =
    cofibrantSourceRoofProductCommaFirstNerve A X Y b ≫
      sourceFrameLeftRoofNerveMap A X.obj Y.obj := by
  let := modelCategory A
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro σ
  let F := ((cofibrantSourceRoofProductCommaAugmentationRoofGraphMap A X Y b ≫
    cofibrantAlgebraHammockGraphInclusionMap A
      (show (cofibrantAlgebraRelativeCategory A).category from X)
      (show (cofibrantAlgebraRelativeCategory A).category from Y) _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.word).app n) σ
  let G := ((cofibrantSourceRoofProductCommaFirstNerve A X Y b ≫
    sourceFrameLeftRoofNerveMap A X.obj Y.obj).app n) σ
  have ho (i : Fin (n.unop.len + 1)) : F.obj i = G.obj i := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagExt.object_ext
    · intro j
      change Fin 3 at j
      fin_cases j <;> rfl
    · intro j
      change Fin 2 at j
      fin_cases j <;> rfl
  apply CategoryTheory.Functor.hext ho
  intro i j f
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagExt.hom_hext (ho i) (ho j)
  intro k
  change Fin 3 at k
  fin_cases k <;> rfl

lemma cofibrantSourceRoofProductCommaAugmentationRoofMap_image :
    cofibrantSourceRoofProductCommaAugmentationRoofMap A X Y b ≫
      cofibrantAlgebraHammockColimitInclusionMap A X Y =
    cofibrantSourceRoofProductCommaFirstNerve A X Y b ≫
      sourceFrameReducedHammockNerveMap A X.obj Y.obj := by
  change (cofibrantSourceRoofProductCommaAugmentationRoofGraphMap A X Y b ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion _ _ _ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.word) ≫ _ = _
  rw [Category.assoc, cofibrantAlgebraHammockColimitInclusionMap_graph,
    ← Category.assoc, ← Category.assoc,
    cofibrantSourceRoofProductCommaAugmentationRoofGraphMap_image]
  exact (Category.assoc _ _ _).trans (congrArg
    (fun g => cofibrantSourceRoofProductCommaFirstNerve A X Y b ≫ g)
    (sourceFrameLeftRoofNerveMap_normalization A X.obj Y.obj))

end SerrePositivity.EInfinity.BarrattEccles
