module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomTargetIdentityCommaProjections
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomTargetCompositionInputs
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.IdentityCommaUnitCapCompositionPaths
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExitLastCompositionPath
/-!
概要：元終域の両単位 cap 道を、元左右 Hom 入力 fiber 内へ持ち上げる。
方針：共有面・単位補正を含む実三角形道の全時間の入力則を使う。
規約：cube の変わる固定辺を直接固定と見なさない。
使われ方：指定二変形への相対比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open DifferentialGraded SSet KST.SConstruction
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R]
  (C D E : Type (max (u + 1) v)) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
  (p : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C E) (q : _root_.SerrePositivity.DifferentialGraded.DGFunctor R D E)
  (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D (dgHomGluingBimodule R C D E p q))
local notation "M" => dgHomGluingBimodule R C D E p q
local notation "IX" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetIdentityCommaObject R C D E p q X
local notation "IY" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetIdentityCommaObject R C D E p q Y

attribute [local irreducible] dgHomGluingBimodule

def dgGluingHomTargetPreCapInputPath :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, max (u + 1) v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComplex R C D M X Y) ⊗ Δ[1] ⟶
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetFirstInputFiber R C D E p q X Y :=
  pullback.lift
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaPreCapCompositionPath.{u, max (u + 1) v} R E IX IY
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetNormalizationHomInput R C D E p q X Y))
    (fst _ (Δ[1] : SSet.{max (u + 1) v}) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max (u + 1) v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightHomMap R C D M X Y)) (by
        erw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaPreCapCompositionPath_over,
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetNormalizationSourceIntervalFamily, Category.assoc])

def dgGluingHomTargetExitCapInputPath :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, max (u + 1) v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComplex R C D M X Y) ⊗ Δ[1] ⟶
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLastInputFiber R C D E p q X Y :=
  pullback.lift
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaExitCapCompositionPath.{u, max (u + 1) v} R E IX IY
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetNormalizationHomInput R C D E p q X Y))
    (fst _ (Δ[1] : SSet.{max (u + 1) v}) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max (u + 1) v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftHomMap R C D M X Y)) (by
        erw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaExitCapCompositionPath_over,
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetNormalizationReplacementIntervalFamily, Category.assoc])

lemma dgGluingHomTargetPreCapInputPath_over :
    dgGluingHomTargetPreCapInputPath R C D E p q X Y ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetFirstInputProjection R C D E p q X Y =
    fst _ (Δ[1] : SSet.{max (u + 1) v}) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max (u + 1) v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightHomMap R C D M X Y) :=
  pullback.lift_snd _ _ _

lemma dgGluingHomTargetExitCapInputPath_over :
    dgGluingHomTargetExitCapInputPath R C D E p q X Y ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLastInputProjection R C D E p q X Y =
    fst _ (Δ[1] : SSet.{max (u + 1) v}) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max (u + 1) v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftHomMap R C D M X Y) :=
  pullback.lift_snd _ _ _

def dgGluingHomTargetExitCollarInputPath :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, max (u + 1) v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComplex R C D M X Y) ⊗ Δ[1] ⟶
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLastInputFiber R C D E p q X Y :=
  pullback.lift
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingExitLastCompositionPath.{u, max (u + 1) v} R E IX IY
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetNormalizationHomInput R C D E p q X Y))
    (fst _ (Δ[1] : SSet.{max (u + 1) v}) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max (u + 1) v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftHomMap R C D M X Y)) (by
        erw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingExitLastCompositionPath_over,
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetNormalizationReplacementIntervalFamily, Category.assoc])

lemma dgGluingHomTargetExitCollarInputPath_over :
    dgGluingHomTargetExitCollarInputPath R C D E p q X Y ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLastInputProjection R C D E p q X Y =
    fst _ (Δ[1] : SSet.{max (u + 1) v}) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max (u + 1) v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftHomMap R C D M X Y) :=
  pullback.lift_snd _ _ _

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
