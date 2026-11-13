module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Objects.FactorZeroObjects
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ComparisonModels.Projections
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ComparisonModels.Size
public import SerrePositivity.DifferentialGraded.Category.Tensor

/-! 片側がホモトピー零である gluing 対象の、二つの実充満 dg 部分圏。 -/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
local notation "G" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M

/-- 右 D 成分が H⁰ で零となる、C 因子の実充満 dg 部分圏。 -/
abbrev DGGluingCFactor :=
  DGFullSubcategory G (fun X => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFactorIsZero R D X.right)

/-- 左 C 成分が H⁰ で零となる、D 因子の実充満 dg 部分圏。 -/
abbrev DGGluingDFactor :=
  DGFullSubcategory G (fun X => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFactorIsZero R C X.left)

def dgGluingCFactorInclusion : DGFunctor R (DGGluingCFactor R C D M) G :=
  dgFullSubcategoryInclusion R G (fun X => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFactorIsZero R D X.right)

def dgGluingDFactorInclusion : DGFunctor R (DGGluingDFactor R C D M) G :=
  dgFullSubcategoryInclusion R G (fun X => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFactorIsZero R C X.left)

/-- C 因子から元の C への比較は、同じ左 dg 射影の制限。 -/
def dgGluingCFactorProjection : DGFunctor R (DGGluingCFactor R C D M) C :=
  (dgGluingCFactorInclusion R C D M).comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeft R C D M)

/-- D 因子から元の D への比較は、同じ右 dg 射影の制限。 -/
def dgGluingDFactorProjection : DGFunctor R (DGGluingDFactor R C D M) D :=
  (dgGluingDFactorInclusion R C D M).comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRight R C D M)

omit [Small.{u} D] in
lemma dgGluingCFactorInclusion_map (X Y : DGGluingCFactor R C D M) :
    (dgGluingCFactorInclusion R C D M).map X Y = 𝟙 (homObject R G X.val Y.val) := rfl

omit [Small.{u} D] in
lemma dgGluingDFactorInclusion_map (X Y : DGGluingDFactor R C D M) :
    (dgGluingDFactorInclusion R C D M).map X Y = 𝟙 (homObject R G X.val Y.val) := rfl

omit [Small.{u} D] in
lemma dgGluingCFactorProjection_obj (X : DGGluingCFactor R C D M) :
    (dgGluingCFactorProjection R C D M).obj X = X.val.left := rfl

omit [Small.{u} D] in
lemma dgGluingDFactorProjection_obj (X : DGGluingDFactor R C D M) :
    (dgGluingDFactorProjection R C D M).obj X = X.val.right := rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
