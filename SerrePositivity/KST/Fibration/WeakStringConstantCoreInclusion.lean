module
public import SerrePositivity.KST.Fibration.WeakStringGappedConstants
public import SerrePositivity.KST.Fibration.WeakStringRelativeCoreRealization
public import SerrePositivity.KST.Fibration.RelativeSKernelSquare

/-! # 元の core 包含と定数 W 列の実対角比較の厳密な照合 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Fibration

/-- 定数 W 列を元の相対 S 対角へ交換すると、元の object/core 比較と core 包含になる。 -/
theorem weakStringObjectConstant_coreInclusion {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    weakStringRealizationConstantDiagonal objectSConstructionFunctor q ≫
      (weakStringObjectRelativeDiagonalIso q).hom =
        objectToCoreSRealization B.obj ≫ simplicialDiagonalFunctor.map
          (relativeSimplicialSConstructionCoreInclusion q.hom) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro v
  change SSet.yonedaEquiv (weakStringGappedRelativeMap q
    ((objectSConstructionFunctor.map (weakStringConstantExact q n.unop)).app n v)) = _
  rw [weakStringGappedRelativeMap_constant]
  apply Subtype.ext
  rfl

/-- 定数 W 列の元の実対角包含は、実現関手間の元の自然変換と厳密に可換。 -/
lemma weakStringRealizationConstantDiagonal_naturality
    {F G : StableModel.{u} ⥤ SSet.{u}} (η : F ⟶ G)
    {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    η.app (sInputModel B) ≫ weakStringRealizationConstantDiagonal G q =
      weakStringRealizationConstantDiagonal F q ≫
        simplicialDiagonalFunctor.map (Functor.whiskerLeft (weakStringStableSimplicial q) η) := by
  apply NatTrans.ext
  funext n
  change (η.app (sInputModel B)).app n ≫ (G.map (weakStringConstantExact q n.unop)).app n =
    (F.map (weakStringConstantExact q n.unop)).app n ≫
      (η.app (weakStringModel q n.unop)).app n
  exact (congr_app (η.naturality (weakStringConstantExact q n.unop)) n).symm

/-- 元の object/core 比較を前合成すると、相対 S の core 包含と定数 W 列の比較は厳密に一致。 -/
lemma relativeSWeakStringCoreComparison_coreInclusion_object
    {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    objectToCoreSRealization B.obj ≫ simplicialDiagonalFunctor.map
      (relativeSimplicialSConstructionCoreInclusion q.hom) ≫
        relativeSWeakStringCoreComparison q =
      objectToCoreSRealization B.obj ≫
        weakStringRealizationConstantDiagonal coreSRealizationFunctor q := by
  calc
    _ = (weakStringRealizationConstantDiagonal objectSConstructionFunctor q ≫
        (weakStringObjectRelativeDiagonalIso q).hom) ≫ relativeSWeakStringCoreComparison q := by
      rw [weakStringObjectConstant_coreInclusion, Category.assoc]
    _ = weakStringRealizationConstantDiagonal objectSConstructionFunctor q ≫
        simplicialDiagonalFunctor.map (weakStringObjectCoreComparison q) := by
      unfold relativeSWeakStringCoreComparison
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
    _ = _ := (weakStringRealizationConstantDiagonal_naturality
      objectCoreRealizationComparison q).symm

end SerrePositivity.KST.Fibration
