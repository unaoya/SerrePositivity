module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetIdentityCommaProjections
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetCompositionInputs
public import SerrePositivity.InfinityCategories.Derived.Gluing.PreNormalizeFirstCompositionPath
public import SerrePositivity.InfinityCategories.Derived.Gluing.PostNormalizeLastCompositionPath
/-!
概要：元終域の補正済み前後正規化道を、元左右 Hom 入力 fiber 内へ持ち上げる。
方針：共有面・単位補正を含む実三角形道の全時間の入力則を使う。
規約：cube の変わる固定辺を直接固定と見なさない。
使われ方：指定二変形への相対比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open DifferentialGraded DGNerve SSet KST.SConstruction
open scoped Simplicial
variable (R : Type u) [CommRing R]
  (C D E : Type (max (u + 1) v)) [DGCategory R C] [Small.{u} C]
  [DGCategory R D] [DGCategory R E] [Small.{u} E]
  (p : DGFunctor R C E) (q : DGFunctor R D E)
  (X Y : DGGluingObject R C D (dgHomGluingBimodule R C D E p q))
local notation "M" => dgHomGluingBimodule R C D E p q
local notation "IX" => dgGluingHomTargetIdentityCommaObject R C D E p q X
local notation "IY" => dgGluingHomTargetIdentityCommaObject R C D E p q Y

attribute [local irreducible] dgHomGluingBimodule

def dgGluingHomTargetPreNormalizationInputPath :
    complexPinchedSpace.{u, max (u + 1) v} (dgGluingHomComplex R C D M X Y) ⊗ Δ[1] ⟶
      dgGluingHomTargetFirstInputFiber R C D E p q X Y :=
  pullback.lift
    (dgGluingPreNormalizeFirstCompositionPath.{u, max (u + 1) v} R E IX IY
      (dgGluingHomTargetNormalizationHomInput R C D E p q X Y))
    (fst _ (Δ[1] : SSet.{max (u + 1) v}) ≫
      complexPinchedMap.{u, max (u + 1) v} (dgGluingRightHomMap R C D M X Y)) (by
        erw [dgGluingPreNormalizeFirstCompositionPath_over,
          dgGluingHomTargetNormalizationSourceIntervalFamily, Category.assoc])

def dgGluingHomTargetPostNormalizationInputPath :
    complexPinchedSpace.{u, max (u + 1) v} (dgGluingHomComplex R C D M X Y) ⊗ Δ[1] ⟶
      dgGluingHomTargetLastInputFiber R C D E p q X Y :=
  pullback.lift
    (dgGluingPostNormalizeLastCompositionPath.{u, max (u + 1) v} R E IX IY
      (dgGluingHomTargetNormalizationHomInput R C D E p q X Y))
    (fst _ (Δ[1] : SSet.{max (u + 1) v}) ≫
      complexPinchedMap.{u, max (u + 1) v} (dgGluingLeftHomMap R C D M X Y)) (by
        erw [dgGluingPostNormalizeLastCompositionPath_over,
          dgGluingHomTargetNormalizationReplacementIntervalFamily, Category.assoc])

lemma dgGluingHomTargetPreNormalizationInputPath_over :
    dgGluingHomTargetPreNormalizationInputPath R C D E p q X Y ≫
      dgGluingHomTargetFirstInputProjection R C D E p q X Y =
    fst _ (Δ[1] : SSet.{max (u + 1) v}) ≫
      complexPinchedMap.{u, max (u + 1) v} (dgGluingRightHomMap R C D M X Y) :=
  pullback.lift_snd _ _ _

lemma dgGluingHomTargetPostNormalizationInputPath_over :
    dgGluingHomTargetPostNormalizationInputPath R C D E p q X Y ≫
      dgGluingHomTargetLastInputProjection R C D E p q X Y =
    fst _ (Δ[1] : SSet.{max (u + 1) v}) ≫
      complexPinchedMap.{u, max (u + 1) v} (dgGluingLeftHomMap R C D M X Y) :=
  pullback.lift_snd _ _ _

end SerrePositivity.InfinityCategories
