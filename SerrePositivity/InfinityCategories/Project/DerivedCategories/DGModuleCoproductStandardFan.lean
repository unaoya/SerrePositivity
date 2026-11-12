module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleCoproductPinchedProducts
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGStandardHomChainMap
public import Mathlib.CategoryTheory.Limits.Types.Products
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
/-!
概要：元の加群余積からの標準 DK 写像空間は、元の包含を脚とする厳密な積となる。
方針：各単体次数の線形方程式の直積表示を、評価による極限反映へ渡す。
規約：全ての面と退化を保持。有限性・compact 性は仮定しない。
使われ方：D-8 c5 の native 余積判定の Hom 条件。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
variable {J : Type u}

def dgModuleCoproductStandardFan (M : J → _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D) (N : _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D) :
    Fan (fun j => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := R)
      (ForgetEnrichment.to (Complex R) (M j)) (ForgetEnrichment.to (Complex R) N)) :=
  Fan.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := R) (ForgetEnrichment.to (Complex R) (∐ M))
    (ForgetEnrichment.to (Complex R) N))
    (fun j => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGStandardHomChainMap.dgStandardHomChainMap (eHomWhiskerRight (Complex R) (Sigma.ι M j) N))

def dgModuleCoproductStandardFan_isLimit (M : J → _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D)
    (N : _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D) : IsLimit (dgModuleCoproductStandardFan R D M N) := by
  apply evaluationJointlyReflectsLimits
  intro n
  refine (isLimitMapConeFanMkEquiv ((evaluation SimplexCategoryᵒᵖ (Type u)).obj n)
    _ _).symm ?_
  let e := Equiv.ofBijective _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCoproductStandard_bijective R D M N n.unop.len)
  let p := Types.productLimitCone (fun j => (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := R)
      (ForgetEnrichment.to (Complex R) (M j)) (ForgetEnrichment.to (Complex R) N)).obj n)
  let c := Fan.mk ((dgModuleCoproductStandardFan R D M N).pt.obj n)
    (fun j => ((dgModuleCoproductStandardFan R D M N).proj j).app n)
  exact IsLimit.ofIsoLimit p.isLimit
    (Cone.ext (c := c) (c' := p.cone) e.toIso (by rintro ⟨j⟩; rfl)).symm

end SerrePositivity.InfinityCategories.Project.DerivedCategories
