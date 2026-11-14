module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ComparisonModels.Postcomposition
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ConeComparisons.CoconeExtraction

/-! 元の閉射の全 Hom 後合成に交換鎖同型を適用する。係数の加群 cone 表示は別途同定する。 -/
@[expose] public section
open CategoryTheory Limits MonoidalCategory CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)
  (X Y Z : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
  (f : ForgetEnrichment.of (Complex R) Y ⟶ ForgetEnrichment.of (Complex R) Z)
local notation "μ" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDifference R C D M X Y
local notation "ν" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDifference R C D M X Z
local notation "p" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPostcompositionComponents R C D M X Y Z f
local notation "k" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPostcomposition R C D M X Y Z f
local notation "hk" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPostcomposition_fst R C D M X Y Z f

/-- 実後合成の同じ第三成分から回収した、双加群値間の鎖写像。 -/
def dgGluingHomConeBottom : M.value X.left Y.right ⟶ M.value X.left Z.right :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconeExtractBottom μ ν p k hk

/-- 実後合成から回収した、全 Hom 成分の正方形の比較ホモトピー。 -/
def dgGluingHomConeHomotopy :
    Cochain (homObject R C X.left Y.left ⊞ homObject R D X.right Y.right)
      (M.value X.left Z.right) (-1) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconeExtractHomotopy μ ν k

/-- 回収した下辺は、元の全第三 cochain と cocone の右包含から得られる。 -/
lemma dgGluingHomConeBottom_cochain :
    Cochain.ofHom (dgGluingHomConeBottom R C D M X Y Z f) =
      (mappingCocone.inr μ).val.comp
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPostcompositionPrimitive R C D M X Y Z f) (by omega) := by
  rw [dgGluingHomConeBottom, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconeExtractBottom_cochain]
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconeExtractBottomCochain
  have he := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPostcomposition_comparison R C D M X Y Z f
  change _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconeExtractPrimitive μ ν k = _ at he
  rw [he]

lemma dgGluingHomConeHomotopy_eq :
    dgGluingHomConeHomotopy R C D M X Y Z f =
      -(mappingCocone.inl μ).comp
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPostcompositionPrimitive R C D M X Y Z f) (zero_add (-1)) := by
  unfold dgGluingHomConeHomotopy _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconeExtractHomotopy
  have he := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPostcomposition_comparison R C D M X Y Z f
  change _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconeExtractPrimitive μ ν k = _ at he
  rw [he]

/-- 元の Hom 後合成の cone に現れる、回収した同じ係数の cone 写像。 -/
def dgGluingHomConeCoefficient : mappingCone p ⟶
    mappingCone (dgGluingHomConeBottom R C D M X Y Z f) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconeExtractConeArrow μ ν p k hk

/-- 元の実 Hom 後合成の標準 cone は、係数 cone 写像の mapping cocone と鎖同型。 -/
def dgGluingHomConeIso : mappingCone k ≅
    mappingCocone (dgGluingHomConeCoefficient R C D M X Y Z f) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconeExtractConeIso μ ν p k hk

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
