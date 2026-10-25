module
public import SerrePositivity.InfinityCategories.Derived.DGModuleCoproductPinchedProducts
public import SerrePositivity.InfinityCategories.Derived.DGStandardHomChainMap
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DoldKanComparison
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
variable {J : Type u}

def dgModuleCoproductStandardFan (M : J → ModuleCategory R D) (N : ModuleCategory R D) :
    Fan (fun j => standardHomSpace (R := R)
      (ForgetEnrichment.to (Complex R) (M j)) (ForgetEnrichment.to (Complex R) N)) :=
  Fan.mk (standardHomSpace (R := R) (ForgetEnrichment.to (Complex R) (∐ M))
    (ForgetEnrichment.to (Complex R) N))
    (fun j => dgStandardHomChainMap (eHomWhiskerRight (Complex R) (Sigma.ι M j) N))

def dgModuleCoproductStandardFan_isLimit (M : J → ModuleCategory R D)
    (N : ModuleCategory R D) : IsLimit (dgModuleCoproductStandardFan R D M N) := by
  apply evaluationJointlyReflectsLimits
  intro n
  refine (isLimitMapConeFanMkEquiv ((evaluation SimplexCategoryᵒᵖ (Type u)).obj n)
    _ _).symm ?_
  let e := Equiv.ofBijective _ (dgModuleCoproductStandard_bijective R D M N n.unop.len)
  let p := Types.productLimitCone (fun j => (standardHomSpace (R := R)
      (ForgetEnrichment.to (Complex R) (M j)) (ForgetEnrichment.to (Complex R) N)).obj n)
  let c := Fan.mk ((dgModuleCoproductStandardFan R D M N).pt.obj n)
    (fun j => ((dgModuleCoproductStandardFan R D M N).proj j).app n)
  exact IsLimit.ofIsoLimit p.isLimit
    (Cone.ext (c := c) (c' := p.cone) e.toIso (by rintro ⟨j⟩; rfl)).symm

end SerrePositivity.InfinityCategories
