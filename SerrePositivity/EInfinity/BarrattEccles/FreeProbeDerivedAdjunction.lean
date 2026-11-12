module

public import SerrePositivity.EInfinity.BarrattEccles.FreeProbeUnitPointInitiality
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.CommaInitialAdjunction

/-!
概要：局所輸送同定を明示入力として、実 U を右随伴とする全 ∞ 随伴を構成する。
方針：元の各単位 comma 候補の実始対象性を公開局所存在判定へ渡す。
規約：入力は未代入の局所輸送同定のみ。F・大域単位・余単位は構成の出力。
使われ方：P-6 の同定を代入した自由忘却随伴と、同じ U の coherent 極限保存。
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

/-- 概要：同じ標準単位比較と同じ候補の普遍輸送の全族同定。
方針：各始域・標的の関手同型の存在を明示する。
規約：P-6 の公開入口を代入するまで、この命題を入力に残す。
使われ方：条件付きの g2-2〜4 の唯一の追加入力。 -/
def FreeProbeUnitTransportCondition : Prop :=
  ∀ (x : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory A) _⦋0⦌) (y : (CAlg_R A) _⦋0⦌),
    Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (derivedFreeProbeUnitIntervalMap A x y)
      (derivedFreeProbeUnitCommaTransportMap A x y))

lemma cAlgForgetDerived_rightAdjoint_exists_of_transport
    (h : FreeProbeUnitTransportCondition A) :
    ∃ F : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory A ⟶ CAlg_R A,
      Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction F (cAlgForgetDerived A)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.exists_qcatAdjunction_of_commaFiberInitial (cAlgForgetDerived A)
  intro x
  exact ⟨derivedFreeProbeUnitCommaVertex A x,
    derivedFreeProbeUnitCommaVertex_isInitial_of_transportIso A x (h x)⟩

def cAlgFreeDerivedOfTransport (h : FreeProbeUnitTransportCondition A) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory A ⟶ CAlg_R A :=
  (cAlgForgetDerived_rightAdjoint_exists_of_transport A h).choose

def cAlgFreeForgetDerivedAdjunctionOfTransport (h : FreeProbeUnitTransportCondition A) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction (cAlgFreeDerivedOfTransport A h) (cAlgForgetDerived A) :=
  Classical.choice (cAlgForgetDerived_rightAdjoint_exists_of_transport A h).choose_spec

/-- 概要：元の候補と構成した全随伴の単位頂点を、同じ comma 内で比較する。
方針：両者の実始対象性から頂点同型を作る。
規約：元の候補の始対象性を、別の単位頂点の始対象性で置き換えない。
使われ方：g1 の元の単位と、条件付きで構成した全随伴との接続。 -/
def derivedFreeProbeUnitCommaAdjunctionIsoOfTransport
    (h : FreeProbeUnitTransportCondition A) (x : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory A) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (X := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber (cAlgForgetDerived A) x)
      (derivedFreeProbeUnitCommaVertex A x)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSectionVertex (cAlgFreeForgetDerivedAdjunctionOfTransport A h).unitHom x) := by
  let : Quasicategory (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber (cAlgForgetDerived A) x) :=
    quasicategory_of_innerFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberProjection (cAlgForgetDerived A) x)
  have hm := (cAlgFreeForgetDerivedAdjunctionOfTransport A h).unitMappingSpaceCondition
  have hi := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitMappingSpaceCondition.unitCommaInitialCondition hm
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.initialVertexIso
    (derivedFreeProbeUnitCommaVertex_isInitial_of_transportIso A x (h x))
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaInitialCondition_iff _).mp hi x)

end SerrePositivity.EInfinity.BarrattEccles
