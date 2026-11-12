module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.SmallKanModel
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.RepresentationPrecompose

/-!
概要：小さい Kan 模型を持つ大きい全空間の点上の表現空間は可縮 Kan。
方針：小さい模型の表現を同値の逆で前合成し、元の全空間の実際の表現を作る。
規約：各次数の小ささは要求しない。表現の存在は小さい模型から証明する。
使われ方：essentially small fiber の相対延長の点上の初期段階。

対応節は Kerodon 4.9（Tag 03PP）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories

/-- 小さい Kan 模型から、元の大きい点上の射影の実際の表現を構成する。 -/
lemma pointWitnessSpace_nonempty_of_smallKanModel (E : SSet.{u + 1}) [KanComplex E]
    (hE : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.HasSmallKanModel E) :
    Nonempty ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessSpace (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportPointProjection E)) _⦋0⦌) := by
  obtain ⟨K, ⟨e⟩⟩ := hE
  let q := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportPointProjection ((SSet.uliftFunctor.{u + 1, u}).obj K.obj)
  let p := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportPointProjection E
  let R : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation q :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessVertexEquiv q).symm (Classical.choice (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallPointWitnessSpace_nonempty K.obj))
  have hf : e.inv ≫ q = p := stdSimplex.isTerminalObj₀.hom_ext _ _
  let S := R.precompose e.inv hf (fun b ↦
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.vertexFiberMap_isQCatEquivalence_of_precompositionEquivalence p q e.inv hf
      e.symm.isQCatEquivalence.isPrecompositionEquivalence b)
  exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessVertex S⟩

/-- 小さい Kan 模型を持つ全空間の点上の表現空間は、追加の存在仮定なしに可縮。 -/
lemma pointWitnessSpace_isContractibleKan_of_smallKanModel
    (E : SSet.{u + 1}) [KanComplex E] (hE : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.HasSmallKanModel E) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessSpace (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportPointProjection E)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointWitnessSpace_isContractibleKan_of_nonempty E
    (pointWitnessSpace_nonempty_of_smallKanModel E hE)

/-- 標準点上の唯一の頂点の fiber の包含は、元の全空間との厳密な同型。 -/
def transportPointFiberIso {E : SSet.{u + 1}}
    (p : E ⟶ (Δ[0] : SSet.{u + 1})) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) ≅ E := by
  have : IsIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) := by
    rw [NatTrans.isIso_iff_isIso_app]
    rintro ⟨⟨n⟩⟩
    rw [isIso_iff_bijective]
    refine ⟨Subtype.val_injective, ?_⟩
    intro x
    exact ⟨⟨x, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.stdSimplex_zero_eq_constant (p.app _ x)⟩, rfl⟩
  exact asIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p (stdSimplex.obj₀Equiv.symm (0 : Fin 1)))

attribute [local instance] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex_of_leftFibration

/-- essentially small fiber の点上の任意の left fibration の表現空間は可縮 Kan。 -/
lemma essentiallySmallPointTransportWitnessSpace_isContractibleKan {E : SSet.{u + 1}}
    (p : E ⟶ (Δ[0] : SSet.{u + 1})) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p]
    (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.HasEssentiallySmallFibers p) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessSpace p) := by
  have : KanComplex E := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportPoint_total_kanComplex p
  have hE : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.HasSmallKanModel E := (hp _).of_equivalence
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (transportPointFiberIso p))
  have he : p = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportPointProjection E := stdSimplex.isTerminalObj₀.hom_ext _ _
  subst p
  exact pointWitnessSpace_isContractibleKan_of_smallKanModel E hE

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories
