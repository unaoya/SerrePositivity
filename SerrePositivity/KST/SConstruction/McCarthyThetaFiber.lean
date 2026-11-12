module
public import SerrePositivity.KST.SConstruction.McCarthyThetaObjects

/-! # 第二の θ の strict 左 fiber への持ち上げ
概要：θ の全時刻でパラメーターを最後の頂点に固定し、同じ左 fiber の族にする。
方針：大域的 θ の subobject の固定を object S の図式で照合する。
規約：fiber 条件を追加仮定にしない。使われ方：ρ の終端と切断の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：θ の全時刻の subobject は最後の頂点の固定単体の像。
方針：可変時刻の θ の subobject と最後の対角零対象の式を照合する。
規約：全単体での厳密な pullback 条件。使われ方：第二ホモトピーの持ち上げ。 -/
lemma mcCarthyThetaFiber_condition (X : StableModel.{u}) {m : ℕ}
    (a : (objectSConstruction X.carrier) _⦋m⦌) :
    mcCarthyThetaObjectMap X a ≫ objectSConstructionFunctor.map (cofiberStableSubobject X) =
      (SSet.const (stdSimplex.obj₀Equiv.symm (Fin.last m)) :
        cofiberSubobjectLeftFiber X a ⊗ Δ[1] ⟶ Δ[m]) ≫ SSet.yonedaEquiv.symm a := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨e, τ⟩
  apply gappedDiagram_injective
  change gappedDiagram ((objectSConstructionFunctor.map (cofiberStableSubobject X)).app
    (Opposite.op ⦋n⦌) (mcCarthyThetaObjectVertex X a e τ)) =
      gappedDiagram ((SSet.yonedaEquiv.symm a).app (Opposite.op ⦋n⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm (Fin.last m)) n))
  rw [gappedDiagram_objectSFunctor_map, mcCarthyThetaObjectVertex_diagram]
  change variableTimeImage _ _ _ ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2), stdSimplex.obj₀Equiv.symm 0) = _
  rw [← cofiberProjection_source, zeroSourceTheta_variableTime_source]
  symm
  change gappedDiagram ((objectSConstruction X.carrier).map
    (SimplexCategory.const ⦋n⦌ ⦋m⦌ (Fin.last m)).op a) = _
  exact gappedDiagram_objectS_const a (Fin.last m)

/-- 概要：θ の族を全時刻で同じ左 fiber へ持ち上げる。
方針：subobject の厳密な等号と定値パラメーターで pullback に入れる。
規約：元の θ の図式を保持。使われ方：第二の実単体ホモトピー。 -/
def mcCarthyThetaFiberMap (X : StableModel.{u}) {m : ℕ}
    (a : (objectSConstruction X.carrier) _⦋m⦌) :
    cofiberSubobjectLeftFiber X a ⊗ Δ[1] ⟶ cofiberSubobjectLeftFiber X a :=
  simplexLeftFiberLift _ a (mcCarthyThetaObjectMap X a)
    (SSet.const (stdSimplex.obj₀Equiv.symm (Fin.last m))) (mcCarthyThetaFiber_condition X a)

/-- 概要：左 fiber に持ち上げた θ の図式は元の object S 値の族。
方針：pullback の第一射影の式。
規約：全単体の等号。使われ方：θ の両端の回収。 -/
lemma mcCarthyThetaFiberMap_projection (X : StableModel.{u}) {m : ℕ}
    (a : (objectSConstruction X.carrier) _⦋m⦌) :
    mcCarthyThetaFiberMap X a ≫ simplexLeftFiberProjection
      (objectSConstructionFunctor.map (cofiberStableSubobject X)) a = mcCarthyThetaObjectMap X a :=
  simplexLeftFiberLift_projection _ _ _ _ _

/-- 概要：左 fiber に持ち上げた θ のパラメーターは最後の頂点で一定。
方針：pullback の第二射影の式。
規約：全単体の等号。使われ方：ρ の終端と切断のパラメーターの照合。 -/
lemma mcCarthyThetaFiberMap_parameter (X : StableModel.{u}) {m : ℕ}
    (a : (objectSConstruction X.carrier) _⦋m⦌) :
    mcCarthyThetaFiberMap X a ≫ simplexLeftFiberParameter
      (objectSConstructionFunctor.map (cofiberStableSubobject X)) a =
        SSet.const (stdSimplex.obj₀Equiv.symm (Fin.last m)) :=
  simplexLeftFiberLift_parameter _ _ _ _ _

end SerrePositivity.KST.SConstruction
