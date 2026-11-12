module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SmallPointWitnessNonempty
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SmallSimplicialSet
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.WitnessTotalIso
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.UniverseKan
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.KanLimits

/-!
概要：各次数で小さい Kan 複体の点上の実際の表現空間は可縮。
方針：全空間を縮小した小さい Kan 複体へ厳密に同定し、小さい点上の可縮性を移す。
規約：表現の存在を追加仮定に置かない。
使われ方：Kerodon Lemma 5.6.9.2（Tag 02SR） の次数ごとに小さい全空間版。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：各次数で小さい Kan 複体の点上の表現空間は可縮 Kan 複体。
方針：次数ごとの縮小の同型で小さい Kan 複体へ移し、実際に構成した表現から可縮性を得る。
規約：非空性と表現の存在を追加仮定にしない。
使われ方：点上の表現空間の可縮性の主経路。 -/
lemma pointWitnessSpace_isContractibleKan_of_small (E : SSet.{u + 1}) [KanComplex E]
    [∀ n, Small.{u} (E.obj n)] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessSpace (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportPointProjection E)) := by
  let K := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallSimplicialSet.{u, u + 1} E
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallSimplicialSetIso.{u, u + 1} E
  have : KanComplex ((SSet.uliftFunctor.{u + 1, u}).obj K) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.kanComplex_of_iso e.symm
  have : KanComplex K := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.kanComplex_of_ulift.{u + 1, u} K
  let p := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportPointProjection ((SSet.uliftFunctor.{u + 1, u}).obj K)
  let q := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportPointProjection E
  have he : e.hom ≫ q = p := stdSimplex.isTerminalObj₀.hom_ext _ _
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.isContractibleKan_of_iso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessTotalIso p q e he).symm
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallPointWitnessSpace_isContractibleKan K)

/-- 概要：標準点上の left fibration の全空間は Kan 複体。
方針：唯一の頂点の fiber の包含が同型であることを各次数で確認する。
規約：全空間の Kan 性を追加仮定に置かない。
使われ方：任意の点射影を標準の点射影へ正規化する。 -/
lemma transportPoint_total_kanComplex {E : SSet.{u}}
    (p : E ⟶ (Δ[0] : SSet.{u})) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] : KanComplex E := by
  let b := stdSimplex.obj₀Equiv.symm (0 : Fin 1)
  have : IsIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b) := by
    rw [NatTrans.isIso_iff_isIso_app]
    rintro ⟨⟨n⟩⟩
    rw [isIso_iff_bijective]
    refine ⟨Subtype.val_injective, ?_⟩
    intro x
    exact ⟨⟨x, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.stdSimplex_zero_eq_constant (p.app _ x)⟩, rfl⟩
  have : KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b) := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex_of_leftFibration p b
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.kanComplex_of_iso (asIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b))

/-- 概要：各次数で小さい全空間を持つ点上の left fibration の表現空間は可縮 Kan。
方針：全空間の Kan 性を射影から得て点への射の一意性で標準形に戻す。
規約：表現の存在も全空間の Kan 性も追加仮定にしない。
使われ方：Kerodon Lemma 5.6.9.2（Tag 02SR） の次数ごとに小さい全空間版。 -/
lemma pointTransportWitnessSpace_isContractibleKan {E : SSet.{u + 1}}
    [∀ n, Small.{u} (E.obj n)] (p : E ⟶ (Δ[0] : SSet.{u + 1})) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessSpace p) := by
  have : KanComplex E := transportPoint_total_kanComplex p
  have hp : p = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportPointProjection E := stdSimplex.isTerminalObj₀.hom_ext _ _
  subst p
  exact pointWitnessSpace_isContractibleKan_of_small E

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
