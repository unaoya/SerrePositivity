module
public import SerrePositivity.InfinityCategories.Derived.Gluing.Postcomposition
public import SerrePositivity.InfinityCategories.Derived.Gluing.CoconeExtraction

/-! 元の閉射の全 Hom 後合成に交換鎖同型を適用する。係数の加群 cone 表示は別途同定する。 -/
@[expose] public section
open CategoryTheory Limits MonoidalCategory CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)
  (X Y Z : DGGluingObject R C D M)
  (f : ForgetEnrichment.of (Complex R) Y ⟶ ForgetEnrichment.of (Complex R) Z)
local notation "μ" => dgGluingDifference R C D M X Y
local notation "ν" => dgGluingDifference R C D M X Z
local notation "p" => dgGluingPostcompositionComponents R C D M X Y Z f
local notation "k" => dgGluingPostcomposition R C D M X Y Z f
local notation "hk" => dgGluingPostcomposition_fst R C D M X Y Z f

/-- 実後合成の同じ第三成分から回収した、双加群値間の鎖写像。 -/
def dgGluingHomConeBottom : M.value X.left Y.right ⟶ M.value X.left Z.right :=
  dgGluingCoconeExtractBottom μ ν p k hk

/-- 実後合成から回収した、全 Hom 成分の正方形の比較ホモトピー。 -/
def dgGluingHomConeHomotopy :
    Cochain (homObject R C X.left Y.left ⊞ homObject R D X.right Y.right)
      (M.value X.left Z.right) (-1) :=
  dgGluingCoconeExtractHomotopy μ ν k

/-- 回収した下辺は、元の全第三 cochain と cocone の右包含から得られる。 -/
lemma dgGluingHomConeBottom_cochain :
    Cochain.ofHom (dgGluingHomConeBottom R C D M X Y Z f) =
      (mappingCocone.inr μ).val.comp
        (dgGluingPostcompositionPrimitive R C D M X Y Z f) (by omega) := by
  rw [dgGluingHomConeBottom, dgGluingCoconeExtractBottom_cochain]
  unfold dgGluingCoconeExtractBottomCochain
  have he := dgGluingPostcomposition_comparison R C D M X Y Z f
  change dgGluingCoconeExtractPrimitive μ ν k = _ at he
  rw [he]

lemma dgGluingHomConeHomotopy_eq :
    dgGluingHomConeHomotopy R C D M X Y Z f =
      -(mappingCocone.inl μ).comp
        (dgGluingPostcompositionPrimitive R C D M X Y Z f) (zero_add (-1)) := by
  unfold dgGluingHomConeHomotopy dgGluingCoconeExtractHomotopy
  have he := dgGluingPostcomposition_comparison R C D M X Y Z f
  change dgGluingCoconeExtractPrimitive μ ν k = _ at he
  rw [he]

/-- 元の Hom 後合成の cone に現れる、回収した同じ係数の cone 写像。 -/
def dgGluingHomConeCoefficient : mappingCone p ⟶
    mappingCone (dgGluingHomConeBottom R C D M X Y Z f) :=
  dgGluingCoconeExtractConeArrow μ ν p k hk

/-- 元の実 Hom 後合成の標準 cone は、係数 cone 写像の mapping cocone と鎖同型。 -/
def dgGluingHomConeIso : mappingCone k ≅
    mappingCocone (dgGluingHomConeCoefficient R C D M X Y Z f) :=
  dgGluingCoconeExtractConeIso μ ν p k hk

end SerrePositivity.InfinityCategories
