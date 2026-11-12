module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGBimoduleCanonicalStrictLift
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelCellLiftFamily
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelCellModelHomFunctor
/-!
概要：任意の元 kernel 射を指定 cell 模型間の実 strict lift へ持ち上げる。
方針：両端の実制限と canonical 双加群分解の厳密な持ち上げを使う。
規約：追加の持ち上げ仮定は不要。使われ方：実模型射作用と元の自然性の照合。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet DifferentialGraded
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] (D E : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
local notation "DC" => _root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R D
local notation "EC" => _root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R E
variable {P0 P1 : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E D}
local notation "p0" => _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D P0
local notation "p1" => _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D P1
local notation "Q0" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellModel R D E p0
local notation "Q1" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellModel R D E p1
local notation "T0" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellResolution R D E p0
local notation "T1" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellResolution R D E p1
def dgKernelCellModelStrictLift (f : P0 ⟶ P1) : Q0 ⟶ Q1 :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleCanonicalResolutionStrictLift R EC DC ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellRestrictionFunctor R D E).map f)
lemma dgKernelCellModelStrictLift_fac (f : P0 ⟶ P1) :
    dgKernelCellModelStrictLift R D E f ≫ (T1).π =
      (T0).π ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellRestrictionFunctor R D E).map f :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleCanonicalResolutionStrictLift_fac R EC DC
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellRestrictionFunctor R D E).map f)
lemma dgKernelCellModelFunctorHomFunctor_map_strictLift (f : P0 ⟶ P1) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellModelFunctorHomFunctor R D E).map f =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R DC EC (BimoduleCategory.underlying R EC DC Q0) ≫
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R E).hom)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R DC EC (BimoduleCategory.underlying R EC DC Q1) ≫
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R E).hom)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R D).inv
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R DC EC (BimoduleCategory.underlying R EC DC Q0))
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R DC EC (BimoduleCategory.underlying R EC DC Q1))
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R E).hom
          ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor R DC EC).map (dgKernelCellModelStrictLift R D E f))) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellModelFunctorHomFunctor_map_raw R D E f (dgKernelCellModelStrictLift R D E f)
    (dgKernelCellModelStrictLift_fac R D E f)
end
end SerrePositivity.InfinityCategories.Project.DerivedCategories
