module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiscreteEmbedding
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorZeroObjects
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeTensor
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGStrictNatTransUnitNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGStrictNatTransClosedIso
public import SerrePositivity.DifferentialGraded.Complexes.TensorZeroCochain
public import SerrePositivity.DifferentialGraded.Functor.DGClosedIsoConjugation

/-!
概要：半自由複体の dg nerve の上で、固定した導来対象との左右テンソルとその対称性を構成する。
方針：左テンソルの dg 作用を半自由複体に制限し、複体の符号つき対称性を通して右テンソルに移す。
使われ方：導来圏内の thick tensor ideal の閉性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor
open CategoryTheory MonoidalCategory DifferentialGraded
open _root_.SerrePositivity.KST.SConstruction
  (dgFunctorClosedConjugate dgFunctorClosedConjugate_naturality)
open scoped _root_.Simplicial
variable {A : Type u} [CommRing A]

namespace FixedTensor

def leftDG (M : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree A) : DGFunctor A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree A) where
  obj N := ⟨M.val ⊗ N.val, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexSemifree_tensor _ _ M.property N.property⟩
  map P Q := (_root_.SerrePositivity.DifferentialGraded.tensorLeftDG M.val).map P.val Q.val
  map_id P := (_root_.SerrePositivity.DifferentialGraded.tensorLeftDG M.val).map_id P.val
  map_comp P Q T := (_root_.SerrePositivity.DifferentialGraded.tensorLeftDG M.val).map_comp P.val Q.val T.val

def rightObj (M N : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree A) : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree A :=
  ⟨N.val ⊗ M.val, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexSemifree_tensor _ _ N.property M.property⟩

def swapIso (M N : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree A) :
    ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) ((leftDG M).obj N) ≅
      ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) (rightObj M N) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeClosedToComplex A).preimageIso (β_ M.val N.val)

def rightDG (M : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree A) : DGFunctor A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree A) :=
  dgFunctorClosedConjugate A (leftDG M) (rightObj M) (swapIso M)

def swapStrict (M : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree A) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans (leftDG M) (rightDG M) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransOfUnitNaturality (fun N => eHomEquiv (Complex A) (swapIso M N).hom)
    (fun P Q => dgFunctorClosedConjugate_naturality A (leftDG M) (rightObj M) (swapIso M) P Q)

end FixedTensor

open FixedTensor

/-- 任意の M との左導来テンソル N ↦ M ⊗ᴸ N。 -/
def tensorLeft (M : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory A) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory A ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory A :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (leftDG (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategoryVertexEquiv A M))

/-- 任意の M との右導来テンソル N ↦ N ⊗ᴸ M。 -/
def tensorWith (M : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory A) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory A ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory A :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (rightDG (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategoryVertexEquiv A M))

/-- 半自由代表上で右テンソルの値は元のテンソル複体である。 -/
lemma tensorWith_vertex (M N : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree A) :
    (tensorWith (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex M)).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex N) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (rightObj M N) := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (rightDG M)).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex N) = _
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex _ _

/-- 符号つき交換同型は固定因子との左右導来テンソルの自然同型を与える。 -/
def tensorWithSymmetry (M : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory A) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (tensorWith M) (tensorLeft M) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransFunctorIsoOfClosedIso (swapStrict (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategoryVertexEquiv A M))
    (swapIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategoryVertexEquiv A M)) (fun _ => rfl)).symm

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor
