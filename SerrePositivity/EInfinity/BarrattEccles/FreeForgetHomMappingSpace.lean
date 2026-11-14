module

public import SerrePositivity.EInfinity.BarrattEccles.FreeForgetHomEquivalence
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Replacements.FixedQuillenTargetInvariance

/-!
# 同じ自由 probe の既存 Map^h への全自然比較

概要：自由忘却 Hom span の元の左端を既存 mappingSpace に接続する。
方針：同じ終域置換への元の比較射のホモトピー同値性を使う。
規約：元の自由 probe・Map^h・全二変数・全単体を保持する。
使われ方：既存 CAlg_R の高次写像空間との照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.DifferentialGraded SerrePositivity.Reedy
open SerrePositivity.HomotopyFunctionComplex
open SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

def freeHomToMappingSpace : (freeProbeFunctor A).op ⋙ sourceFrameHom A ⟶
    (freeProbeFunctor A).op ⋙ mappingSpace A :=
  Functor.whiskerLeft (freeProbeFunctor A).op (sourceFrameHomComparison A)

lemma freeHomToMappingSpace_homotopyEquivalence
    (X : (Complex A)ᵒᵖ) (B : (operad A).Algebra) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (((freeHomToMappingSpace A).app X).app B) := by
  let := modelCategory A
  let q := cosimplicialResolutionFamily (mappingCofibrantFactorization A)
  let r := mappingFibrantFactorization A
  have : IsFibrant ((𝟭 (operad A).Algebra).obj B) := isFibrant A B
  have := fibrantTarget_isFibrant r B
  have : WeakEquivalence ((fibrantTargetComparison r).app B) :=
    ⟨fibrantTargetComparison_weakEquivalence r B⟩
  exact _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.frameHom_target_homotopyEquivalence _
    (q.cofibrant ((freeProbeFunctor A).obj X.unop))
    (q.atObject ((freeProbeFunctor A).obj X.unop)).homotopicallyConstant
    ((fibrantTargetComparison r).app B)

end SerrePositivity.EInfinity.BarrattEccles
