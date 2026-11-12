module

public import SerrePositivity.EInfinity.Interface.Core
public import SerrePositivity.InfinityCategories.Derived.Tensor.Fixed
public import SerrePositivity.InfinityCategories.Derived.HZero
public import SerrePositivity.InfinityCategories.Derived.DGClosedEdges
public import SerrePositivity.InfinityCategories.Stable.BinaryCoproductCocone
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
open SerrePositivity.InfinityCategories.DGNerve
open scoped Simplicial
attribute [local instance] HasDerivedCategory.standard
variable (S : Type u) [CommRing S]

/-- 具体的な semifree 複体間の鎖写像を、D(S) の指定射の類へ送る。 -/
def derivedComplexHom {P Q : Semifree S} (f : P.val ⟶ Q.val) :
    (SSet.HomotopyCategory.mk (Simplex.vertex P) : (derivedInfinityCategory S).HomotopyCategory) ⟶
      SSet.HomotopyCategory.mk (Simplex.vertex Q) :=
  SSet.Truncated.HomotopyCategory.homMk (dgClosedEdge S (Semifree S)
    ((semifreeClosedToComplex S).preimage
      (X := ForgetEnrichment.of (Complex S) P) (Y := ForgetEnrichment.of (Complex S) Q) f))

/-- 固定された二頂点のテンソルは、同じ代表の実際のテンソル複体である。 -/
lemma tensorWith_representative_vertex (x y : (derivedInfinityCategory S) _⦋0⦌) :
    atVertex (tensorWith y) x = Simplex.vertex
      (FixedTensor.rightObj (derivedInfinityCategoryVertexEquiv S y)
        (derivedInfinityCategoryVertexEquiv S x)) := by
  let P := derivedInfinityCategoryVertexEquiv S x
  let Q := derivedInfinityCategoryVertexEquiv S y
  have hx : Simplex.vertex P = x := (derivedInfinityCategoryVertexEquiv S).symm_apply_apply x
  have hy : Simplex.vertex Q = y := (derivedInfinityCategoryVertexEquiv S).symm_apply_apply y
  exact (congrArg₂ (fun b a => atVertex (tensorWith b) a) hy.symm hx.symm).trans
    (tensorWith_vertex Q P)

/-- 右因子の単位の代表から作る、左因子の標準テンソル射。 -/
def derivedTensorInlHom (x y : (derivedInfinityCategory S) _⦋0⦌)
    (unitY : 𝟙_ (Complex S) ⟶ (derivedInfinityCategoryVertexEquiv S y).val) :
    (SSet.HomotopyCategory.mk x : (derivedInfinityCategory S).HomotopyCategory) ⟶
      SSet.HomotopyCategory.mk (atVertex (tensorWith y) x) :=
  eqToHom (congrArg SSet.HomotopyCategory.mk
    ((derivedInfinityCategoryVertexEquiv S).symm_apply_apply x).symm) ≫
  derivedComplexHom S
    (P := derivedInfinityCategoryVertexEquiv S x)
    (Q := FixedTensor.rightObj (derivedInfinityCategoryVertexEquiv S y)
      (derivedInfinityCategoryVertexEquiv S x))
    ((ρ_ _).inv ≫ (𝟙 _ ⊗ₘ unitY)) ≫
  eqToHom (congrArg SSet.HomotopyCategory.mk (tensorWith_representative_vertex S x y).symm)

/-- 左因子の単位の代表から作る、右因子の標準テンソル射。 -/
def derivedTensorInrHom (x y : (derivedInfinityCategory S) _⦋0⦌)
    (unitX : 𝟙_ (Complex S) ⟶ (derivedInfinityCategoryVertexEquiv S x).val) :
    (SSet.HomotopyCategory.mk y : (derivedInfinityCategory S).HomotopyCategory) ⟶
      SSet.HomotopyCategory.mk (atVertex (tensorWith y) x) :=
  eqToHom (congrArg SSet.HomotopyCategory.mk
    ((derivedInfinityCategoryVertexEquiv S).symm_apply_apply y).symm) ≫
  derivedComplexHom S
    (P := derivedInfinityCategoryVertexEquiv S y)
    (Q := FixedTensor.rightObj (derivedInfinityCategoryVertexEquiv S y)
      (derivedInfinityCategoryVertexEquiv S x))
    ((λ_ _).inv ≫ (unitX ⊗ₘ 𝟙 _)) ≫
  eqToHom (congrArg SSet.HomotopyCategory.mk (tensorWith_representative_vertex S x y).symm)

/-- 複体のテンソル単位の H⁰ は基底環そのもの。 -/
def complexUnitHZeroIso : (𝟙_ (Complex S)).homology 0 ≅ ModuleCat.of S S := by
  letI := HomologicalComplex.monoidalCategoryStruct (ModuleCat S) (.up ℤ)
  exact HomologicalComplex.singleObjHomologySelfIso (.up ℤ) (0 : ℤ) (ModuleCat.of S S)

/-- native な頂点の H⁰ を、その同じ代表の H⁰ と比較する。 -/
def vertexHZeroRepresentativeIso (x : (derivedInfinityCategory S) _⦋0⦌) :
    (((homotopyCategoryBridge (derivedInfinityCategory S)).inverse ⋙
      derivedInfinityHomologyFunctor S 0).obj (SSet.HomotopyCategory.mk x)) ≅
        (derivedInfinityCategoryVertexEquiv S x).val.homology 0 :=
  derivedInfinityHZeroIso S x

end SerrePositivity.EInfinity
