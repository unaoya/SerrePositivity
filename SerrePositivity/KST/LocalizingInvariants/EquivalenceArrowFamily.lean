module

public import SerrePositivity.KST.LocalizingInvariants.EquivalencePathFamily
public import SerrePositivity.InfinityCategories.F1B.ConstantFunctor
public import SerrePositivity.InfinityCategories.Stable.TrivialFibrationComparisonProjection

/-!
概要：可逆矢印の全族を、同じ始点の恒等矢印族へ比較する。
方針：可逆 path の始点評価の可縮な fiber で比較し、元の矢印圏へ戻す。
規約：比較は始点で恒等となる。使われ方：一般商の包含上の普遍差を対角へ比較する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.EquivalenceArrowFamily
variable {A X : SSet.{u}} [Quasicategory X]
  (a : A ⟶ (ihom (Δ[1] : SSet.{u})).obj X)
  (ha : ∀ x, IsEquivalencePathVertex (a.app (Opposite.op ⦋0⦌) x))

def pathLift : A ⟶ equivalencePath X := fullSubcomplexLift IsEquivalencePathVertex a ha

lemma pathLift_inclusion : pathLift a ha ≫ equivalencePathι X = a :=
  fullSubcomplexLift_ι _ _ _

lemma pathLift_source : pathLift a ha ≫ equivalencePathEndpoint X 0 =
    a ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
  rw [equivalencePathEndpoint, ← Category.assoc, pathLift_inclusion]

def sourceRefl : A ⟶ equivalencePath X :=
  (a ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) ≫ equivalencePathRefl X

lemma sameSource : pathLift a ha ≫ equivalencePathEndpoint X 0 =
    sourceRefl a ≫ equivalencePathEndpoint X 0 := by
  rw [pathLift_source, sourceRefl, Category.assoc, equivalencePathRefl_endpoint,
    Category.comp_id]

def pathComparison : FunctorIso (pathLift a ha) (sourceRefl a) :=
  functorIsoOfTrivialKanFibration (equivalencePathEndpoint X 0) _ _ (sameSource a ha)

lemma pathComparison_source_arrow :
    Arrow.mk (FunctorIso.postcomp (pathComparison a ha) (equivalencePathEndpoint X 0)).hom =
      Arrow.mk (𝟙 (HomotopyCategory.mk (functorVertex
        (sourceRefl a ≫ equivalencePathEndpoint X 0)) : hoFunctor.obj ((ihom A).obj X))) :=
  functorIsoOfTrivialKanFibration_projection_arrow _ _ _ (sameSource a ha)

def comparison : FunctorIso a
    ((a ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) ≫
      constantFunctorMap (Δ[1] : SSet.{u}) X) := by
  have e := FunctorIso.postcomp (pathComparison a ha) (equivalencePathι X)
  rw [pathLift_inclusion] at e
  simpa only [sourceRefl, Category.assoc, equivalencePathRefl_ι, constantFunctorMap] using e

end SerrePositivity.KST.LocalizingInvariants.EquivalenceArrowFamily
