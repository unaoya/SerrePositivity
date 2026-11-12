module

public import SerrePositivity.EInfinity.BarrattEccles.FreeProbeDerivedAdjunction
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CommaLocalUnitTransportComparison
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.ConstantHomFaithful

/-!
概要：P-6 の局所輸送同型に、同じ実自由単位と元の comma 候補を代入する。
方針：零単体の定値 Hom 類で回収辺を認識し、元の標準比較の等式へ戻す。
規約：F・大域単位・局所輸送同定を仮定せず、公開済みの局所同型を使う。
使われ方：条件付き g2-2〜4 の輸送条件を証明する入口。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet
open SerrePositivity.InfinityCategories

open scoped Simplicial
variable (A : Type u) [CommRing A]

lemma derivedFreeProbeUnitCommaTargetFiberArrow_hom
    (x : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory A) _⦋0⦌) :
    Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.commaTargetFiberArrow (cAlgForgetDerived A) x (derivedFreeProbeVertex A x)
        (derivedFreeProbeUnitCommaTargetFiberVertex A x)).toTruncated =
      derivedFreeProbeUnitHom A x := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.constantFunctorHomMap_injective
    (A := (Δ[0] : SSet.{u + 1})) (stdSimplex.obj₀Equiv.symm 0)
    x ((cAlgForgetDerived A).app (Opposite.op ⦋0⦌) (derivedFreeProbeVertex A x))
  have hh := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomotopyHom_heq_of_raw_eq
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHomotopy (SSet.const (X := (Δ[0] : SSet.{u + 1}))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.commaTargetFiberArrow (cAlgForgetDerived A) x
        (derivedFreeProbeVertex A x) (derivedFreeProbeUnitCommaTargetFiberVertex A x)))))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberHomotopy (SSet.const (derivedFreeProbeUnitCommaVertex A x) :
      Δ[0] ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber (cAlgForgetDerived A) x))
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.commaTargetFiber_constant_homotopy (A := (Δ[0] : SSet.{u + 1}))
      (derivedFreeProbeUnitCommaTargetFiberVertex A x))
  have he := eq_of_heq (hh.trans (derivedFreeProbeUnitCommaVertex_hom A x))
  change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom _ = _ at he
  rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.intervalFamilyHom_const_edge] at he
  exact he

lemma unitIntervalMapAt_derivedFreeProbeUnitCommaTargetFiberVertex
    (x : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory A) _⦋0⦌) (y : (CAlg_R A) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.unitIntervalMapAt (derivedFreeProbeUnitCommaTargetFiberVertex A x) y =
      derivedFreeProbeUnitIntervalMap A x y := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.unitIntervalMapAt, derivedFreeProbeUnitCommaTargetFiberArrow_hom]
  rfl

def derivedFreeProbeUnitIntervalMap_transportIso
    (x : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory A) _⦋0⦌) (y : (CAlg_R A) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (derivedFreeProbeUnitIntervalMap A x y)
      (derivedFreeProbeUnitCommaTransportMap A x y) := by
  simpa only [unitIntervalMapAt_derivedFreeProbeUnitCommaTargetFiberVertex,
    derivedFreeProbeUnitCommaTransportMap] using
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.unitIntervalMapAt_commaTransportIso (derivedFreeProbeUnitCommaTargetFiberVertex A x) y

lemma freeProbeUnitTransportCondition : FreeProbeUnitTransportCondition A := by
  intro x y
  exact ⟨derivedFreeProbeUnitIntervalMap_transportIso A x y⟩

end SerrePositivity.EInfinity.BarrattEccles
