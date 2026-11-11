module
public import SerrePositivity.KST.SConstruction.PointedMappingPathSections
public import SerrePositivity.KST.SConstruction.BoundaryAssemblyNaturality

/-! # 一方向比較の逆射の可縮な選択空間
概要：元の一方向比較の逆を mapping path 切断の族で制御する。
方針：既存の全基点 π 同型を切断空間の一般定理に適用する。
規約：既存の逆射の定義を変更せず、同じ点つきホモトピー成分を回収する。
使われ方：元の BF K 模型を保つ逆射の高次整合性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open Spectra Spectra.PointedMapping
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 一方向比較の mapping path 切断による逆射の選択空間。 -/
def oneDirectionKanInverseChoices (r : ℕ) (X : StableModel.{u}) : SSet.{u} :=
  pointedMappingPathSectionSpace ((oneDirectionKanComparisonNat r).app X)

/-- 一方向比較の逆射の選択空間は可縮 Kan。 -/
lemma oneDirectionKanInverseChoices_isContractibleKan (r : ℕ) (X : StableModel.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (oneDirectionKanInverseChoices r X) :=
  pointedMappingPathSectionSpace_isContractibleKan _
    (oneDirectionReducedComparison_kan_piIsomorphism r X)

/-- 任意の逆射の選択頂点が与える元の Kan 模型間の実際の射。 -/
def oneDirectionKanInverseAt (r : ℕ) (X : StableModel.{u})
    (v : (oneDirectionKanInverseChoices r X) _⦋0⦌) :
    (boundaryKanRealizationFunctor r).obj X ⟶ (oneDirectionKanRealizationFunctor r).obj X :=
  pointedMappingPathInverseAt ((oneDirectionKanComparisonNat r).app X) v

/-- 任意の逆射の選択は既存の Whitehead の逆射と同じ点つきホモトピー成分。 -/
lemma oneDirectionKanInverseAt_component (r : ℕ) (X : StableModel.{u})
    (v : (oneDirectionKanInverseChoices r X) _⦋0⦌) :
    componentOf (oneDirectionKanComparisonInverse r X) = componentOf (oneDirectionKanInverseAt r X v) := by
  have hv := pointedMappingPathInverseAt_homotopy ((oneDirectionKanComparisonNat r).app X)
    (oneDirectionReducedComparison_kan_piIsomorphism r X) v
  have h := pointedComponentInverse_naturality
    ((oneDirectionKanComparisonNat r).app X) ((oneDirectionKanComparisonNat r).app X)
    (oneDirectionKanComparisonInverse r X) (oneDirectionKanInverseAt r X v) (𝟙 _) (𝟙 _)
    (((piZero_eq_iff_pointedHomotopy _ _).mpr hv.1).symm)
    (((piZero_eq_iff_pointedHomotopy _ _).mpr (oneDirectionKanComparisonInverse_homotopy r X)).symm)
    (by simp)
  simpa only [Category.comp_id, Category.id_comp] using h

/-- 逆射の高次選択を既存部分を保って任意の単射に沿い補完できる。 -/
lemma oneDirectionKanInverseChoices_relative_lifting (r : ℕ) (X : StableModel.{u})
    {S T : SSet.{u}} (j : S ⟶ T) [Mono j] (a : S ⟶ oneDirectionKanInverseChoices r X) :
    ∃ b : T ⟶ oneDirectionKanInverseChoices r X, j ≫ b = a :=
  pointedMappingPathSectionSpace_relative_lifting _
    (oneDirectionReducedComparison_kan_piIsomorphism r X) j a

end SerrePositivity.KST.SConstruction
