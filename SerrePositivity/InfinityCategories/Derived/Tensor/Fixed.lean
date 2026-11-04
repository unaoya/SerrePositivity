module

public import SerrePositivity.InfinityCategories.Derived.DiscreteEmbedding
public import SerrePositivity.InfinityCategories.Derived.DGFunctorZeroObjects
public import SerrePositivity.InfinityCategories.Derived.SemifreeTensor
public import SerrePositivity.InfinityCategories.Derived.DGStrictNatTransUnitNaturality
public import SerrePositivity.InfinityCategories.Derived.DGStrictNatTransClosedIso
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory DifferentialGraded DGNerve
open SerrePositivity.KST.SConstruction
  (dgFunctorClosedConjugate dgFunctorClosedConjugate_naturality)
open scoped Simplicial
variable {A : Type u} [CommRing A]

namespace FixedTensor

def leftDG (M : Semifree A) : DGFunctor A (Semifree A) (Semifree A) where
  obj N := ⟨M.val ⊗ N.val, complexSemifree_tensor _ _ M.property N.property⟩
  map P Q := (tensorLeftDG M.val).map P.val Q.val
  map_id P := (tensorLeftDG M.val).map_id P.val
  map_comp P Q T := (tensorLeftDG M.val).map_comp P.val Q.val T.val

def rightObj (M N : Semifree A) : Semifree A :=
  ⟨N.val ⊗ M.val, complexSemifree_tensor _ _ N.property M.property⟩

def swapIso (M N : Semifree A) :
    ForgetEnrichment.of (Complex A) ((leftDG M).obj N) ≅
      ForgetEnrichment.of (Complex A) (rightObj M N) :=
  (semifreeClosedToComplex A).preimageIso (β_ M.val N.val)

def rightDG (M : Semifree A) : DGFunctor A (Semifree A) (Semifree A) :=
  dgFunctorClosedConjugate A (leftDG M) (rightObj M) (swapIso M)

def swapStrict (M : Semifree A) : StrictNatTrans (leftDG M) (rightDG M) :=
  dgStrictNatTransOfUnitNaturality (fun N => eHomEquiv (Complex A) (swapIso M N).hom)
    (fun P Q => dgFunctorClosedConjugate_naturality A (leftDG M) (rightObj M) (swapIso M) P Q)

end FixedTensor

open FixedTensor

/-- 任意の M との左導来テンソル N ↦ M ⊗ᴸ N。 -/
def tensorLeft (M : (derivedInfinityCategory A) _⦋0⦌) :
    derivedInfinityCategory A ⟶ derivedInfinityCategory A :=
  dgNerve.map (leftDG (derivedInfinityCategoryVertexEquiv A M))

/-- 任意の M との右導来テンソル N ↦ N ⊗ᴸ M。 -/
def tensorWith (M : (derivedInfinityCategory A) _⦋0⦌) :
    derivedInfinityCategory A ⟶ derivedInfinityCategory A :=
  dgNerve.map (rightDG (derivedInfinityCategoryVertexEquiv A M))

/-- 半自由代表上で右テンソルの値は元のテンソル複体である。 -/
lemma tensorWith_vertex (M N : Semifree A) :
    (tensorWith (Simplex.vertex M)).app (Opposite.op ⦋0⦌) (Simplex.vertex N) =
      Simplex.vertex (rightObj M N) := by
  change (dgNerve.map (rightDG M)).app (Opposite.op ⦋0⦌) (Simplex.vertex N) = _
  exact dgFunctorNerve_vertex _ _

/-- 符号つき交換同型は固定因子との左右導来テンソルの自然同型を与える。 -/
def tensorWithSymmetry (M : (derivedInfinityCategory A) _⦋0⦌) :
    FunctorIso (tensorWith M) (tensorLeft M) :=
  (dgStrictNatTransFunctorIsoOfClosedIso (swapStrict (derivedInfinityCategoryVertexEquiv A M))
    (swapIso (derivedInfinityCategoryVertexEquiv A M)) (fun _ => rfl)).symm

end SerrePositivity.InfinityCategories
