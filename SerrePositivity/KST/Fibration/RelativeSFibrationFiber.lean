module
public import SerrePositivity.KST.Fibration.RelativeSKernelBasepoint
public import SerrePositivity.KST.Fibration.RelativeSKernelRealizationPullback
public import SerrePositivity.KST.Fibration.ContractibleBaseFiberComparison

/-! # 元の相対 S の core 包含の指定した基点上のファイバー -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.Comparison
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration

/-- 元の包含側の零対象の基点を、元の相対 S の包含で周囲の対角へ送る。 -/
def relativeSFibrationBasepoint
    {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
    (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) :
    stdSimplex.obj ⦋0⦌ ⟶ simplicialDiagonalFunctor.obj (relativeSimplicialSConstruction q.hom) :=
  relativeSKernelBasepoint h ≫
    simplicialDiagonalFunctor.map (relativeSimplicialFunctorMap i q.hom)

/-- 商との比較前の、元の core 包含の同じ基点上の実ホモトピーファイバー模型。 -/
def relativeSFibrationFiber
    {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
    (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) : SSet.{u} :=
  homotopyPullbackObject
    (simplicialDiagonalFunctor.map (relativeSimplicialSConstructionCoreInclusion q.hom))
    (relativeSFibrationBasepoint h)

/-- 元の core S(D) の実現と、元の相対 core 包含の指定した fiber との局所化同型。 -/
def relativeSFibrationFiberIso
    {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
    (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) :
    AnodyneHomotopy.anodyneQ.obj (coreSRealizationFunctor.obj (sInputModel A)) ≅
      AnodyneHomotopy.anodyneQ.obj (relativeSFibrationFiber h) :=
  contractibleBaseFiberIso (relativeSKernelRealizationSquare i q).flip
    ((isHomotopyPullback_flip_iff _).mpr (relativeSKernelRealizationSquare_homotopyPullback h))
    (relativeSKernelDiagonal_toPoint_localized_isIso h) (relativeSKernelBasepoint h)

/-- 同じ fiber 模型の元の左射影。 -/
def relativeSFibrationFiberProjection
    {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
    (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) :
    relativeSFibrationFiber h ⟶ coreSRealizationFunctor.obj (sInputModel B) :=
  pullback.fst _ _

/-- 指定した fiber との同型は、元の Verdier 包含の core S 実現射を回収する。 -/
theorem relativeSFibrationFiberIso_hom_projection
    {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
    (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) :
    (relativeSFibrationFiberIso h).hom ≫
        AnodyneHomotopy.anodyneQ.map (relativeSFibrationFiberProjection h) =
      AnodyneHomotopy.anodyneQ.map (simplicialDiagonalFunctor.map (coreSExactMap i)) :=
  contractibleBaseFiberIso_hom_fst (relativeSKernelRealizationSquare i q).flip
    ((isHomotopyPullback_flip_iff _).mpr (relativeSKernelRealizationSquare_homotopyPullback h))
    (relativeSKernelDiagonal_toPoint_localized_isIso h) (relativeSKernelBasepoint h)

end SerrePositivity.KST.Fibration
