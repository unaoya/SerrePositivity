module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetCommaHom
/-!
概要：元終域の comma 比較は元の二つの Hom 成分と第三 cochain を回収する。
方針：同じ cocone 写像の第一射影・第二 cochain の式を評価する。
規約：比較は元の Hom gluing の全整数次数で厳密に一致する。
使われ方：元二脚を持つ lax pullback 比較の単位・合成と全 prism の接続に用いる。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits CochainComplex HomComplex DifferentialGraded
open KST.SConstruction
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (E : Type z) [DGCategory R E] [Small.{u} E]
  (p : DGFunctor R C E) (q : DGFunctor R D E)
variable (X Y : DGGluingObject R C D (dgHomGluingBimodule R C D E p q))
include X Y
lemma dgGluingHomTargetCommaHomMap_source :
    dgGluingHomTargetCommaHomMap R C D E p q X Y ≫
      dgFunctorCommaSourceHomMap R D E q (dgGluingHomTargetCommaObject R C D E p q X)
          (dgGluingHomTargetCommaObject R C D E p q Y) = dgGluingRightHomMap R C D
          (dgHomGluingBimodule R C D E p q) X Y := by
  dsimp only [dgFunctorCommaSourceHomMap, dgGluingRightHomMap]
  rw [dgGluingHomTargetCommaHomMap, ← Category.assoc,
    complexMappingCoconeMap_fst, Category.assoc]
  dsimp only [dgGluingHomTargetCommaComponents]
  erw [biprod.lift_fst]
lemma dgGluingHomTargetCommaHomMap_replacement :
    dgGluingHomTargetCommaHomMap R C D E p q X Y ≫
      dgFunctorCommaReplacementHomMap R D E q (dgGluingHomTargetCommaObject R C D E p q X)
          (dgGluingHomTargetCommaObject R C D E p q Y) =
    dgGluingLeftHomMap R C D (dgHomGluingBimodule R C D E p q) X Y ≫ p.map X.left Y.left := by
  dsimp only [dgFunctorCommaReplacementHomMap, dgGluingLeftHomMap]
  rw [dgGluingHomTargetCommaHomMap, ← Category.assoc,
    complexMappingCoconeMap_fst, Category.assoc]
  dsimp only [dgGluingHomTargetCommaComponents]
  erw [biprod.lift_snd]
  exact (Category.assoc _ _ _).symm
lemma dgGluingHomTargetCommaHomMap_comparison :
    dgFunctorCommaHomComparison R D E q (dgGluingHomTargetCommaObject R C D E p q X)
        (dgGluingHomTargetCommaObject R C D E p q Y) _
      (dgGluingHomTargetCommaHomMap R C D E p q X Y) = dgGluingHomPrimitive R C D
          (dgHomGluingBimodule R C D E p q) X Y := by
  dsimp only [dgFunctorCommaHomComparison, dgFunctorCommaPrimitive,
    dgGluingHomTargetCommaHomMap, dgGluingHomPrimitive]
  rw [complexMappingCoconeMap_snd]
  exact Cochain.comp_id _
end SerrePositivity.InfinityCategories
