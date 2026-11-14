module

public import SerrePositivity.EInfinity.Interface.Core
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.Fixed
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.HomotopyModels.HZero
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.DGClosedEdges
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.BinaryCoproductCocone
public import Mathlib.Algebra.Homology.SingleHomology

/-!
# 導来テンソルの二つの標準射

概要：HA 3.2.4.7 のテンソル比較が保つ二つの標準射を記述する。
方針：単位射の閉次数零の代表から、複体の単位子による二つの射を作る。
規約：E∞ 代数の模型は参照せず、固定された D(S) と離散入力の比較だけを使う。
使われ方：EInfinityTheory の coproduct_tensor_legs。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity
open CategoryTheory Limits MonoidalCategory Opposite SSet
open SerrePositivity.InfinityCategories SerrePositivity.DifferentialGraded

open scoped Simplicial
attribute [local instance] HasDerivedCategory.standard
variable (S : Type u) [CommRing S]

/-- 具体的な semifree 複体間の鎖写像を、D(S) の指定射の類へ送る。 -/
def derivedComplexHom {P Q : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S} (f : P.val ⟶ Q.val) :
    (SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex P) : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory S).HomotopyCategory) ⟶
      SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Q) :=
  SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S)
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeClosedToComplex S).preimage
      (X := ForgetEnrichment.of (Complex S) P) (Y := ForgetEnrichment.of (Complex S) Q) f))

/-- 固定された二頂点のテンソルは、同じ代表の実際のテンソル複体である。 -/
lemma tensorWith_representative_vertex (x y : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory S) _⦋0⦌) :
    atVertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.tensorWith y) x = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.FixedTensor.rightObj (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategoryVertexEquiv S y)
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategoryVertexEquiv S x)) := by
  let P := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategoryVertexEquiv S x
  let Q := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategoryVertexEquiv S y
  have hx : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex P = x := (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategoryVertexEquiv S).symm_apply_apply x
  have hy : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Q = y := (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategoryVertexEquiv S).symm_apply_apply y
  exact (congrArg₂ (fun b a => atVertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.tensorWith b) a) hy.symm hx.symm).trans
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.tensorWith_vertex Q P)

/-- 右因子の単位の代表から作る、左因子の標準テンソル射。 -/
def derivedTensorInlHom (x y : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory S) _⦋0⦌)
    (unitY : 𝟙_ (Complex S) ⟶ (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategoryVertexEquiv S y).val) :
    (SSet.HomotopyCategory.mk x : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory S).HomotopyCategory) ⟶
      SSet.HomotopyCategory.mk (atVertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.tensorWith y) x) :=
  eqToHom (congrArg SSet.HomotopyCategory.mk
    ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategoryVertexEquiv S).symm_apply_apply x).symm) ≫
  derivedComplexHom S
    (P := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategoryVertexEquiv S x)
    (Q := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.FixedTensor.rightObj (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategoryVertexEquiv S y)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategoryVertexEquiv S x))
    ((ρ_ _).inv ≫ (𝟙 _ ⊗ₘ unitY)) ≫
  eqToHom (congrArg SSet.HomotopyCategory.mk (tensorWith_representative_vertex S x y).symm)

/-- 左因子の単位の代表から作る、右因子の標準テンソル射。 -/
def derivedTensorInrHom (x y : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory S) _⦋0⦌)
    (unitX : 𝟙_ (Complex S) ⟶ (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategoryVertexEquiv S x).val) :
    (SSet.HomotopyCategory.mk y : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory S).HomotopyCategory) ⟶
      SSet.HomotopyCategory.mk (atVertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.tensorWith y) x) :=
  eqToHom (congrArg SSet.HomotopyCategory.mk
    ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategoryVertexEquiv S).symm_apply_apply y).symm) ≫
  derivedComplexHom S
    (P := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategoryVertexEquiv S y)
    (Q := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.FixedTensor.rightObj (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategoryVertexEquiv S y)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategoryVertexEquiv S x))
    ((λ_ _).inv ≫ (unitX ⊗ₘ 𝟙 _)) ≫
  eqToHom (congrArg SSet.HomotopyCategory.mk (tensorWith_representative_vertex S x y).symm)

/-- 複体のテンソル単位の H⁰ は基底環そのもの。 -/
def complexUnitHZeroIso : (𝟙_ (Complex S)).homology 0 ≅ ModuleCat.of S S := by
  letI := HomologicalComplex.monoidalCategoryStruct (ModuleCat S) (.up ℤ)
  exact HomologicalComplex.singleObjHomologySelfIso (.up ℤ) (0 : ℤ) (ModuleCat.of S S)

/-- native な頂点の H⁰ を、その同じ代表の H⁰ と比較する。 -/
def vertexHZeroRepresentativeIso (x : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory S) _⦋0⦌) :
    (((_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyCategoryBridge (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory S)).inverse ⋙
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomologyFunctor S 0).obj (SSet.HomotopyCategory.mk x)) ≅
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategoryVertexEquiv S x).val.homology 0 :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHZeroIso S x

end SerrePositivity.EInfinity
