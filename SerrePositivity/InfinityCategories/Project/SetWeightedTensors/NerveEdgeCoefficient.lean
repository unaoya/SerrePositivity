module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.NerveSimplexCoefficient
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.InvertibleEdgeLifting

/-!
概要：weighted nerve の辺の最後の係数の可逆性を相対係数評価へ移す。
方針：底変換は係数を保ち、終対象への評価は可逆辺を保存する。
規約：係数の Kan 性・quasicategory 性は不要。
使われ方：Cat∞ 値 unstraightening の cocartesian 辺の判定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.SetWeightedTensors

/-- 辺の最後の係数で表される辺が可逆であるという条件。 -/
def WeightedNerveCoefficientInvertible {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) (e : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F) _⦋1⦌) : Prop :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (SSet.yonedaEquiv (e.2.app (Fin.last 1))))

/-- 底変換は辺の最後の係数とその可逆性を保つ。 -/
lemma weightedNerveBaseMap_coefficientInvertible {C D : Type u}
    [Category.{u} C] [Category.{u} D] (H : D ⥤ C) (F : C ⥤ SSet.{u})
    (e : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve (H ⋙ F)) _⦋1⦌) :
    WeightedNerveCoefficientInvertible F ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveBaseMap H F).app _ e) ↔
      WeightedNerveCoefficientInvertible (H ⋙ F) e := Iff.rfl

/-- 終対象への係数評価は最後の係数が可逆な辺を可逆辺へ送る。 -/
lemma weightedNerveTerminalEvaluation_edge_invertible {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {t : C} (ht : IsTerminal t)
    (e : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F) _⦋1⦌) (he : WeightedNerveCoefficientInvertible F e) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveTerminalEvaluation F ht).app _ e)) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (SSet.yonedaEquiv
    (e.2.app (Fin.last 1) ≫ F.map (ht.from (e.1.obj (Fin.last 1))))))
  rw [SSet.yonedaEquiv_comp]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr
    (e := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (SSet.yonedaEquiv (e.2.app (Fin.last 1)))).map
      ((truncation 2).map (F.map (ht.from (e.1.obj (Fin.last 1))))))
    (f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex ((F.map (ht.from (e.1.obj (Fin.last 1)))).app _
      (SSet.yonedaEquiv (e.2.app (Fin.last 1))))) rfl).mp
    (he.map (F.map (ht.from (e.1.obj (Fin.last 1)))))

/-- 相対係数評価は、元の辺の最後の係数が可逆なら可逆な辺を与える。 -/
lemma weightedNerveSimplexCoefficient_edge_invertible {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {n : ℕ} (σ : ComposableArrows C n) {T : SSet.{u}}
    (a : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F) (b : T ⟶ (Δ[n] : SSet.{u}))
    (ha : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F = b ≫ SSet.yonedaEquiv.symm σ)
    (e : T _⦋1⦌) (he : WeightedNerveCoefficientInvertible F (a.app _ e)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexCoefficient F σ a b ha).app _ e)) := by
  let I := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexIndexFunctor σ
  have h : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F =
      (b ≫ (stdSimplex.isoNerve.{u} n).hom) ≫ nerveMap I := by
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexIndexFunctor_projection]
    exact ha
  let l := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveBaseChangeLift I F a (b ≫ (stdSimplex.isoNerve.{u} n).hom) h
  have hl : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveBaseMap I F).app _ (l.app _ e) = a.app _ e :=
    congrArg (fun f => f.app _ e) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveBaseChangeLift_base I F a _ h)
  have hi : WeightedNerveCoefficientInvertible (I ⋙ F) (l.app _ e) := by
    apply (weightedNerveBaseMap_coefficientInvertible I F _).mp
    rw [hl]
    exact he
  exact weightedNerveTerminalEvaluation_edge_invertible (I ⋙ F)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexIndexTerminal.{u} n) (l.app _ e) hi

end SerrePositivity.InfinityCategories.Project.SetWeightedTensors
