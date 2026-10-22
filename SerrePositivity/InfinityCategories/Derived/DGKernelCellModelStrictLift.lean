module
public import SerrePositivity.InfinityCategories.Derived.DGBimoduleCanonicalStrictLift
public import SerrePositivity.InfinityCategories.Derived.DGKernelCellLiftFamily
public import SerrePositivity.InfinityCategories.Derived.DGKernelCellModelHomFunctor
/-!
概要：任意の元 kernel 射を指定 cell 模型間の実 strict lift へ持ち上げる。
方針：両端の実制限と canonical 双加群分解の厳密な持ち上げを使う。
規約：追加の持ち上げ仮定は不要。使われ方：実模型射作用と元の自然性の照合。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet DifferentialGraded DGNerve
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] (D E : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
local notation "DC" => DGCategoryCellResolution.Source R D
local notation "EC" => DGCategoryCellResolution.Source R E
variable {P0 P1 : BimoduleCategory R E D}
local notation "p0" => BimoduleCategory.underlying R E D P0
local notation "p1" => BimoduleCategory.underlying R E D P1
local notation "Q0" => dgKernelCellModel R D E p0
local notation "Q1" => dgKernelCellModel R D E p1
local notation "T0" => dgKernelCellResolution R D E p0
local notation "T1" => dgKernelCellResolution R D E p1
def dgKernelCellModelStrictLift (f : P0 ⟶ P1) : Q0 ⟶ Q1 :=
  dgBimoduleCanonicalResolutionStrictLift R EC DC ((dgKernelCellRestrictionFunctor R D E).map f)
lemma dgKernelCellModelStrictLift_fac (f : P0 ⟶ P1) :
    dgKernelCellModelStrictLift R D E f ≫ (T1).π =
      (T0).π ≫ (dgKernelCellRestrictionFunctor R D E).map f :=
  dgBimoduleCanonicalResolutionStrictLift_fac R EC DC
    ((dgKernelCellRestrictionFunctor R D E).map f)
lemma dgKernelCellModelFunctorHomFunctor_map_strictLift (f : P0 ⟶ P1) :
    (dgKernelCellModelFunctorHomFunctor R D E).map f =
      functorHomPrecomp
        (dgKernelDerivedInfinity R DC EC (BimoduleCategory.underlying R EC DC Q0) ≫
          (dgCellModuleSourceEquivalence R E).hom)
        (dgKernelDerivedInfinity R DC EC (BimoduleCategory.underlying R EC DC Q1) ≫
          (dgCellModuleSourceEquivalence R E).hom)
        (dgCellModuleSourceEquivalence R D).inv
        (functorHomPostcomp
          (dgKernelDerivedInfinity R DC EC (BimoduleCategory.underlying R EC DC Q0))
          (dgKernelDerivedInfinity R DC EC (BimoduleCategory.underlying R EC DC Q1))
          (dgCellModuleSourceEquivalence R E).hom
          ((dgKernelDerivedFunctorHomFunctor R DC EC).map (dgKernelCellModelStrictLift R D E f))) :=
  dgKernelCellModelFunctorHomFunctor_map_raw R D E f (dgKernelCellModelStrictLift R D E f)
    (dgKernelCellModelStrictLift_fac R D E f)
end
end SerrePositivity.InfinityCategories
