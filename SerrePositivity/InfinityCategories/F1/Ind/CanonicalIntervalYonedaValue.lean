module

public import SerrePositivity.InfinityCategories.Core.Equivalence
public import SerrePositivity.InfinityCategories.Core.EquivalenceCalculus
public import SerrePositivity.InfinityCategories.Core.FunctorEvaluation
public import SerrePositivity.InfinityCategories.Core.InnerFiber
public import SerrePositivity.InfinityCategories.Core.VertexFiber
public import SerrePositivity.InfinityCategories.F1.Categories.CatInfinity
public import SerrePositivity.InfinityCategories.F1.Categories.PointedSpaces
public import SerrePositivity.InfinityCategories.F1.Coherent.Vertices
public import SerrePositivity.InfinityCategories.F1.Fibrations.CartesianFibration
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalMappingPostcompositionVertices
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalMappingSpace
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftUnstraighteningFiberValue
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftUnstraighteningTransformationFamily
public import SerrePositivity.InfinityCategories.F1.Transport.ParametrizedFiberTransport
public import SerrePositivity.InfinityCategories.F1.Universe.InnerFibration
public import SerrePositivity.InfinityCategories.F1.Universe.Kan
public import SerrePositivity.InfinityCategories.F1.Yoneda.CanonicalYonedaFiberTransport
public import SerrePositivity.InfinityCategories.F1.Yoneda.YonedaInfinityConstruction
public import SerrePositivity.InfinityCategories.F1.Ind.DensityFiberTransformationFamily
public import SerrePositivity.InfinityCategories.F1.Ind.ElementsYonedaSliceInterval

/-!
概要：Tw 全体から取る同じ恒等点で、大域密度変換の全 fiber 作用を評価する。
方針：F1 の canonical な評価の同値と、全パラメータ付き普遍輸送比較を再利用する。
規約：元の大域密度変換を使い、評価点は同じ Tw 全体の復元から取る。
使われ方：同じ恒等点復元射上の密度値写像との比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {C : SSet.{u}} [Quasicategory C]
  (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u}) (x : C _⦋0⦌)
local notation "z" => F.app (Opposite.op ⦋0⦌) (ULift.up (SSet.opObjEquiv.symm x))
abbrev presheafDensityCanonicalSourceValue :=
  (representablePresheafInfinity x).app (Opposite.op ⦋0⦌)
    (ULift.up (SSet.opObjEquiv.symm x))
local notation "a" => presheafDensityCanonicalSourceValue x

/-- Tw 全体から取る同じ恒等点で、元の区間写像空間を元の前層値へ評価する。 -/
def canonicalIntervalYonedaEvaluation :=
  canonicalYonedaTransformationFiberEvaluation x F ≫ (pointedSpaceFiberValueEquivalence z).hom

/-- 元の同じ恒等点からの区間評価自身が同値。 -/
lemma canonicalIntervalYonedaEvaluation_isQCatEquivalence :
    IsQCatEquivalence (canonicalIntervalYonedaEvaluation F x) :=
  (canonicalYonedaTransformationFiberEvaluation_isQCatEquivalence x F).comp
    (pointedSpaceFiberValueEquivalence z).isQCatEquivalence

/-- 元の大域密度変換を同じ Tw の恒等点で評価した全 fiber 上の値写像。 -/
def presheafDensityCanonicalFiberValue :=
  presheafDensityOriginalFiberInterval F x ≫ canonicalIntervalYonedaEvaluation F x

/-- 元の全 fiber をパラメータとする、同じ対象で評価した区間の族。 -/
def presheafDensityCanonicalFiberInterval :=
  presheafDensityOriginalFiberInterval F x ≫
    intervalMappingPostOfEq (evaluateFunctorAt (ULift.up (SSet.opObjEquiv.symm x)))
      (functorVertex (representablePresheafInfinity x)) (functorVertex F)
      (evaluateFunctorAt_functorVertex _ _) (evaluateFunctorAt_functorVertex _ _)

/-- 同じ区間の全パラメータ付き輸送を、Tw の元の恒等点で評価する。 -/
def presheafDensityCanonicalTransportValue :=
  presheafDensityCanonicalFiberInterval F x ≫ parametrizedFiberTransport pointedSpaceProjection a z ≫
    evaluateFunctorAt (canonicalYonedaPointedIdentity x) ≫
      (pointedSpaceFiberValueEquivalence z).hom

/-- 元の大域密度変換の恒等点評価と同じ区間族の普遍輸送を、全 fiber 上で比較する。 -/
def presheafDensityCanonicalFiberTransportIso :
    FunctorIso (presheafDensityCanonicalFiberValue F x)
      (presheafDensityCanonicalTransportValue F x) := by
  have h := FunctorIso.precomp
    (FunctorIso.postcomp (canonicalYonedaTransformationFiberEvaluation_parametrizedIso x F)
      (pointedSpaceFiberValueEquivalence z).hom) (presheafDensityOriginalFiberInterval F x)
  simpa only [presheafDensityCanonicalFiberValue, canonicalIntervalYonedaEvaluation,
    presheafDensityCanonicalTransportValue, presheafDensityCanonicalFiberInterval,
    presheafDensityCanonicalSourceValue, Category.assoc] using h

end SerrePositivity.InfinityCategories.F2.Ind
