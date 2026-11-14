module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.PointFunctorEvaluation

/-!
概要：一点上の相対関手単体集合と、元の射の頂点 fiber の厳密な同型。
方針：fiber の射を点因子に定値な族として curry し、評価の単射性で逆合成を確認する。
規約：元の射 p の充填性は要求しない。
使われ方：Kerodon §5.3.1（Tag 035D）、始対象への制限による strict transport の値の回収。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 概要：標準零単体からの射は唯一の頂点の像に定値。
方針：標準零単体の終対象性と定値射の合成の式を使う。
規約：標的 B は任意。
使われ方：Kerodon §5.3.1（Tag 035D）、一点上の相対関手空間の固定条件。 -/
lemma pointDiagram_eq_const {B : SSet.{u}} (a : (Δ[0] : SSet.{u}) ⟶ B) :
    a = SSet.const (a.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 0)) := by
  calc
    a = (𝟙 (Δ[0] : SSet.{u})) ≫ a := (Category.id_comp a).symm
    _ = SSet.const (stdSimplex.obj₀Equiv.symm 0) ≫ a :=
      congrArg (fun q ↦ q ≫ a) (stdSimplex.isTerminalObj₀.hom_ext _ _)
    _ = _ := SSet.const_comp _ a

/-- 概要：fiber の元を一点に定値な相対関手へ写す。
方針：第二射影に fiber の包含を続けた図式を curry する。
規約：固定する底の図式は任意の Δ[0] からの射。
使われ方：Kerodon §5.3.1（Tag 035D）、一点上の相対評価の逆。 -/
def relativePointFunctorInverse {E B : SSet.{u}} (p : E ⟶ B)
    (a : (Δ[0] : SSet.{u}) ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p (a.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 0)) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p a := by
  let b := a.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 0)
  let F := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b
  have hR : fst (Δ[0] : SSet.{u}) F ≫ a = SSet.const b :=
    (congrArg (fun q ↦ fst (Δ[0] : SSet.{u}) F ≫ q) (pointDiagram_eq_const a)).trans
      (SSet.comp_const _ b)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorCurry (snd (Δ[0] : SSet.{u}) F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b) (by
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.comp_const, hR])

/-- 概要：fiber の元を相対関手にして一点で評価すると元に戻る。
方針：curry の頂点評価の式と第二射影の計算を使う。
規約：fiber の包含後に厳密な等式を確認する。
使われ方：Kerodon §5.3.1（Tag 035D）、一点上の相対評価の切断。 -/
lemma relativePointFunctorInverse_evaluate {E B : SSet.{u}} (p : E ⟶ B)
    (a : (Δ[0] : SSet.{u}) ⟶ B) :
    relativePointFunctorInverse p a ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorEvaluate p a (stdSimplex.obj₀Equiv.symm 0) = 𝟙 _ := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext p (a.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 0))
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorEvaluate_ι]
  change curry (snd (Δ[0] : SSet.{u}) _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p _) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0) =
    𝟙 _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.curry_evaluateFunctorAt_vertex, ← Category.assoc, lift_snd,
    Category.id_comp]

/-- 概要：一点上の相対関手の評価は元の fiber への厳密な同型。
方針：評価の切断を構成し、一点からの関手の評価の単射性で逆合成も示す。
規約：p は任意の単体集合の射。
使われ方：Kerodon §5.3.1（Tag 035D）、strict transport の始対象での評価と fiber の同定。 -/
def relativePointFunctorIso {E B : SSet.{u}} (p : E ⟶ B)
    (a : (Δ[0] : SSet.{u}) ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p a ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p (a.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 0)) where
  hom := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorEvaluate p a (stdSimplex.obj₀Equiv.symm 0)
  inv := relativePointFunctorInverse p a
  inv_hom_id := relativePointFunctorInverse_evaluate p a
  hom_inv_id := by
    let e := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorEvaluate p a (stdSimplex.obj₀Equiv.symm 0)
    let j := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p (a.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 0))
    have : Mono ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.pointFunctorEvaluationIso E).hom) := inferInstance
    have : Mono (e ≫ j) := by
      change Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorEvaluate p a (stdSimplex.obj₀Equiv.symm 0) ≫ j)
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorEvaluate_ι]
      exact inferInstanceAs (Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((ihom (Δ[0] : SSet.{u})).map p)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.pointFunctorEvaluationIso E).hom))
    have : Mono e := mono_of_mono e j
    apply (cancel_mono e).1
    change (e ≫ relativePointFunctorInverse p a) ≫ e = (𝟙 _) ≫ e
    rw [Category.assoc, relativePointFunctorInverse_evaluate,
      Category.comp_id, Category.id_comp]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "4.1.4.6" (partial := component) "仮定：相対関手の始域が Δ0 で、底への写像が [1] を選ぶ（HA の T¹ の場合）。結論：一点上の相対関手空間の評価が指定ファイバーとの同型となる（評価による同型の成分に一致）。非単位的 A₁ のマーク条件が空になる同定は含まれない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativePointFunctorIso
