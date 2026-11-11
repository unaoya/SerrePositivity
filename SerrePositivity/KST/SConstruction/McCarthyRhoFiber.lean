module
public import SerrePositivity.KST.SConstruction.McCarthyRhoFiberObjects

/-! # McCarthy の ρ の左 fiber 内の族
概要：ρ の図式と動かしたパラメーターを同じ左 fiber の射に束ねる。
方針：subobject の厳密回収で pullback の可換条件を証明する。
規約：左 fiber 条件を追加仮定にしない。使われ方：加法性の実ホモトピー。
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

/-- 概要：左 fiber のパラメーターを時刻に沿って最後の頂点へ動かす射。
方針：標準単体の最後の頂点への収縮に元のパラメーターを入れる。
規約：時刻は第二因子に置く。使われ方：ρ の基底の動き。 -/
def mcCarthyRhoFiberParameterMap (X : StableModel.{u}) {m : ℕ}
    (a : (objectSConstruction X.carrier) _⦋m⦌) :
    cofiberSubobjectLeftFiber X a ⊗ Δ[1] ⟶ Δ[m] :=
  (β_ (cofiberSubobjectLeftFiber X a) (Δ[1] : SSet.{u})).hom ≫
    (Δ[1] ◁ simplexLeftFiberParameter
      (objectSConstructionFunctor.map (cofiberStableSubobject X)) a) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.prismLastContraction m

/-- 概要：ρ の単体的な族は動かしたパラメーターの固定単体上にある。
方針：図式への単射な対応で subobject の厳密回収を使う。
規約：全単体での pullback の可換条件。使われ方：左 fiber への無条件な持ち上げ。 -/
lemma mcCarthyRhoFiber_condition (X : StableModel.{u}) {m : ℕ}
    (a : (objectSConstruction X.carrier) _⦋m⦌) :
    mcCarthyRhoFiberObjectMap X a ≫ objectSConstructionFunctor.map (cofiberStableSubobject X) =
      mcCarthyRhoFiberParameterMap X a ≫ SSet.yonedaEquiv.symm a := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨e, τ⟩
  apply gappedDiagram_injective
  change gappedDiagram ((objectSConstructionFunctor.map (cofiberStableSubobject X)).app
    (Opposite.op ⦋n⦌) (mcCarthyRhoFiberObjectVertex X a e τ)) =
      gappedDiagram ((SSet.yonedaEquiv.symm a).app (Opposite.op ⦋n⦌)
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.prismLastContraction m).app (Opposite.op ⦋n⦌)
          (τ, mcCarthyFiberParameter X a e)))
  rw [gappedDiagram_objectSFunctor_map, SSet.yonedaEquiv_symm_app,
    gappedDiagram_objectS_map, mcCarthyMovedOrder_simplex, mcCarthyRhoFiberObjectVertex_diagram]
  change mcCarthyRho _ _ _ _ _ _ ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2), stdSimplex.obj₀Equiv.symm 0) = _
  rw [← cofiberProjection_source]
  exact mcCarthyRho_source _ _ _ _ _ _

/-- 概要：ρ は同じ左 fiber 内の実際の単体的な族を与える。
方針：証明した subobject の等号で strict pullback に持ち上げる。
規約：元の C 内の選択を保持する。使われ方：恒等射から零 subobject 側へのホモトピー。 -/
def mcCarthyRhoFiberMap (X : StableModel.{u}) {m : ℕ}
    (a : (objectSConstruction X.carrier) _⦋m⦌) :
    cofiberSubobjectLeftFiber X a ⊗ Δ[1] ⟶ cofiberSubobjectLeftFiber X a :=
  simplexLeftFiberLift _ a (mcCarthyRhoFiberObjectMap X a) (mcCarthyRhoFiberParameterMap X a)
    (mcCarthyRhoFiber_condition X a)

/-- 概要：左 fiber 値の ρ の図式は元の object S 値の族。
方針：pullback の第一射影の式。
規約：全単体での厳密な等号。使われ方：端点と quotient の照合。 -/
lemma mcCarthyRhoFiberMap_projection (X : StableModel.{u}) {m : ℕ}
    (a : (objectSConstruction X.carrier) _⦋m⦌) :
    mcCarthyRhoFiberMap X a ≫ simplexLeftFiberProjection
      (objectSConstructionFunctor.map (cofiberStableSubobject X)) a =
        mcCarthyRhoFiberObjectMap X a :=
  simplexLeftFiberLift_projection _ _ _ _ _

/-- 概要：左 fiber 値の ρ のパラメーターは最後の頂点への収縮。
方針：pullback の第二射影の式。
規約：全単体での厳密な等号。使われ方：端点での固定単体の回収。 -/
lemma mcCarthyRhoFiberMap_parameter (X : StableModel.{u}) {m : ℕ}
    (a : (objectSConstruction X.carrier) _⦋m⦌) :
    mcCarthyRhoFiberMap X a ≫ simplexLeftFiberParameter
      (objectSConstructionFunctor.map (cofiberStableSubobject X)) a =
        mcCarthyRhoFiberParameterMap X a :=
  simplexLeftFiberLift_parameter _ _ _ _ _

end SerrePositivity.KST.SConstruction
