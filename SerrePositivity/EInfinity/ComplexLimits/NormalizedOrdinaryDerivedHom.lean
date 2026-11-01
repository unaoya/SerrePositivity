module

public import SerrePositivity.EInfinity.ComplexLimits.NormalizedProbeDerivedSpan
public import SerrePositivity.EInfinity.ComplexLimits.DerivedSourceValues
public import SerrePositivity.EInfinity.ComplexLimits.ProbeDerivedSourceVertex
public import SerrePositivity.InfinityCategories.Core.Roof.PinchedEndpointTransport

/-!
# 元の通常導来源の同じ端点を持つ実正規化 Hom 比較

概要：probe の実 D(R) Hom 比較を、元の X,Y の通常導来源の値へ戻す。
方針：実値の等式と元の probe 比較の全関手同型を使う。
規約：元の導来単位の構成と同じ始域比較の逆を前合成する。
使われ方：元の単位誘導射と同じ ∞ 写像空間 Hom span の接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open DGNerve SerrePositivity.InfinityCategories.HomotopyLimits
open SerrePositivity.HomotopyFunctionComplex
open scoped Simplicial
variable (A : Type u) [CommRing A]

def normalizedProbeDerivedEndpointIso (X Y : Complex A) :
    pinchedHom (X := derivedInfinityCategory A)
      ((kProjectiveDerivedSource A).app (Opposite.op ⦋0⦌)
        (Simplex.vertex (framedLimitKProjectiveProbe A X)))
      (Simplex.vertex (complexSemifreeResolutionValue A Y)) ≅
    pinchedHom (X := derivedInfinityCategory A)
      ((complexOrdinaryDerivedSource A).app (Opposite.op ⦋0⦌)
        (nerveVertex ((framedLimitProbeFunctor A).obj X)))
      ((complexOrdinaryDerivedSource A).app (Opposite.op ⦋0⦌) (nerveVertex Y)) :=
  pinchedEndpointIso
    ((kProjectiveDerivedSource_vertex_eq A (framedLimitKProjectiveProbe A X)).trans
      (complexOrdinaryDerivedSource_vertex_eq A ((framedLimitProbeFunctor A).obj X)).symm)
    (complexOrdinaryDerivedSource_vertex_eq A Y).symm

def normalizedOrdinaryDerivedHomMap (X Y : Complex A) :
    SSet.uliftFunctor.{u + 1, u}.obj
      (((normalizedProbeTensorHom A).obj (Opposite.op X)).obj
        (complexSemifreeResolutionValue A Y).val) ⟶
    pinchedHom (X := derivedInfinityCategory A)
      ((complexOrdinaryDerivedSource A).app (Opposite.op ⦋0⦌) (nerveVertex X))
      ((complexOrdinaryDerivedSource A).app (Opposite.op ⦋0⦌) (nerveVertex Y)) :=
  normalizedProbeDerivedHomMap A X Y ≫ (normalizedProbeDerivedEndpointIso A X Y).hom ≫
    PinchedInterval.precompose _
      (complexProbeDerivedSourceVertexIso A X).inv

open SSet.modelCategoryQuillen in
lemma normalizedOrdinaryDerivedHomMap_homotopyEquivalence (X Y : Complex A) :
    IsSimplicialHomotopyEquivalence (normalizedOrdinaryDerivedHomMap A X Y) := by
  have : KanComplex (SSet.uliftFunctor.{u + 1, u}.obj
      (((normalizedProbeTensorHom A).obj (Opposite.op X)).obj
        (complexSemifreeResolutionValue A Y).val)) :=
    HomotopicalAlgebra.isFibrant_of_fibration
      (normalizedKProjectiveHomIso A (framedLimitKProjectiveProbe A X)
        (semifreeKProjectiveTarget A Y)).hom
  have h₀ := normalizedProbeDerivedHomMap_homotopyEquivalence A X Y
  have h₁ := DoldKanComparison.simplicialHomotopyEquivalence_iso_hom
    (normalizedProbeDerivedEndpointIso A X Y)
  have h₂ := (pinchedPrecompose_isQCatEquivalence_of_isIso
    (complexProbeDerivedSourceVertexIso A X).inv
    ((complexOrdinaryDerivedSource A).app (Opposite.op ⦋0⦌)
      (nerveVertex Y))).isSimplicialHomotopyEquivalence
  exact h₀.comp (h₁.comp h₂)

end SerrePositivity.EInfinity.ComplexLimits
