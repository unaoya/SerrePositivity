module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.RightUnitRawReturn

/-!
概要：固定右単位の母写像を元の随伴対応の固定右ファイバーへ持ち上げる。
方針：左右の関手と同じ単位辺の回収によって指定単位条件を移す。
規約：元の実単位を変えず、元の e1 の写像空間へ戻す。
使われ方：元の右ファイバーと可縮単位空間との同型の逆射。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：母空間へ戻した左関手は元の固定右単位の左関手。
方針：底の第一成分と全関手圏への左回収の等式を関手の表示の逆へ移す。
規約：元の単体集合の射として等しい。
使われ方：戻した実単位の左端点の照合。 -/
lemma rightAdjointUnitRaw_leftFunctor (C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u})
    (w : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrRMappingSpace D C _⦋0⦌) (x : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.RightAdjointUnitSpace C D w.val _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.unitLeftFunctor ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rightAdjointUnitRaw C D w).app (Opposite.op ⦋0⦌) x) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rightUnitLeftFunctor x.val.val := by
  have hb := congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) x) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rightAdjointUnitRaw_base C D w)
  have hl := congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) x) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.rightAdjointUnitLeft_ι C D w.val)
  exact congrArg (fun z ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv C.obj D.obj).symm z)
    ((congrArg (fun z : (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrLMappingSpace C D ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrRMappingSpace D C) _⦋0⦌ ↦
      z.1.val.val) hb).trans hl)

/-- 概要：母空間へ戻した右関手は固定した元の右関手。
方針：底の第二成分を零次の定値写像の値で計算する。
規約：元の右関手の厳密な等式。
使われ方：戻した実単位の右端点の照合。 -/
lemma rightAdjointUnitRaw_rightFunctor (C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u})
    (w : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrRMappingSpace D C _⦋0⦌) (x : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.RightAdjointUnitSpace C D w.val _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.unitRightFunctor ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rightAdjointUnitRaw C D w).app (Opposite.op ⦋0⦌) x) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rightVertexFunctor w.val := by
  have hb := congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) x) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rightAdjointUnitRaw_base C D w)
  have hw : (SSet.const w : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.RightAdjointUnitSpace C D w.val ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrRMappingSpace D C).app
      (Opposite.op ⦋0⦌) x = w := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero w
  exact (congrArg (fun z : (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrLMappingSpace C D ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrRMappingSpace D C) _⦋0⦌ ↦
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rightVertexFunctor z.2.val) hb).trans
      (congrArg (fun z : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrRMappingSpace D C _⦋0⦌ ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rightVertexFunctor z.val) hw)

/-- 概要：母空間へ戻した単位辺は元の固定右単位の辺。
方針：coslice 成分の保存を元の辺の回収へ移す。
規約：元の一次単体を変更しない。
使われ方：指定単位条件の同じ Hom 類を回収する。 -/
lemma rightAdjointUnitRaw_unitEdge (C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u})
    (w : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrRMappingSpace D C _⦋0⦌) (x : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.RightAdjointUnitSpace C D w.val _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.unitCorrespondenceEdge ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rightAdjointUnitRaw C D w).app (Opposite.op ⦋0⦌) x)).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rightUnitEdge x.val.val).edge := by
  exact congrArg (fun s ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceUnderVertexEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (𝟙 C.obj)) s).edge)
    (congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) x) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rightAdjointUnitRaw_unit C D w))

/-- 概要：母空間へ戻した実単位は元の随伴単位の条件を満たす。
方針：左右の端点の回収と同じ単位辺の Hom 類で条件を移す。
規約：新たな随伴の存在や単位の選択を仮定しない。
使われ方：元の随伴単位の全部分空間への逆射の持ち上げ。 -/
lemma rightAdjointUnitRaw_unitCondition (C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u})
    (w : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrRMappingSpace D C _⦋0⦌) (x : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.RightAdjointUnitSpace C D w.val _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitMappingSpaceCondition
      (F := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.unitLeftFunctor ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rightAdjointUnitRaw C D w).app (Opposite.op ⦋0⦌) x))
      (G := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.unitRightFunctor ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rightAdjointUnitRaw C D w).app (Opposite.op ⦋0⦌) x))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.unitCorrespondenceHom ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rightAdjointUnitRaw C D w).app (Opposite.op ⦋0⦌) x)) := by
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.edgeHom_heq
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.unitCorrespondenceEdge ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rightAdjointUnitRaw C D w).app (Opposite.op ⦋0⦌) x))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rightUnitEdge x.val.val) (rightAdjointUnitRaw_unitEdge C D w x)
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.unitCondition_transport (rightAdjointUnitRaw_leftFunctor C D w x)
    (rightAdjointUnitRaw_rightFunctor C D w x) _ _ he).mpr
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex x.val)

/-- 概要：固定右の単位空間から元の随伴単位条件の全部分複体へ戻す。
方針：元の実単位の母写像を同じ指定単位条件で持ち上げる。
規約：元の単位の全単体を保持する。
使われ方：元の随伴対応への逆射の構成。 -/
def rightAdjointUnitToFullSpace (C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u})
    (w : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrRMappingSpace D C _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.RightAdjointUnitSpace C D w.val ⟶
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.RawAdjointUnitSpace C D)
      (fun v ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitMappingSpaceCondition (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.unitCorrespondenceHom v)) : SSet.{u + 1}) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rightAdjointUnitRaw C D w) (rightAdjointUnitRaw_unitCondition C D w)

/-- 概要：固定右の単位空間から元の随伴単位の core へ戻す。
方針：Kan 始域から元の全部分空間の core へ持ち上げる。
規約：元の実単位の対応空間を標的とする。
使われ方：元の右ファイバーへの逆射の構成。 -/
def rightAdjointUnitReturn (C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u})
    (w : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrRMappingSpace D C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.RightAdjointUnitSpace C D w.val ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.AdjointUnitMappingSpace C D :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.kanCoreMap (rightAdjointUnitToFullSpace C D w)

/-- 概要：元の対応へ戻した射を母空間へ含めると同じ実単位の母写像。
方針：core と全部分複体の包含を順に相殺する。
規約：全次数の射の厳密な等式。
使われ方：固定右条件と往復の射の検証。 -/
lemma rightAdjointUnitReturn_underlying (C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u})
    (w : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrRMappingSpace D C _⦋0⦌) :
    rightAdjointUnitReturn C D w ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.adjointUnitUnderlying C D = _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rightAdjointUnitRaw C D w := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.kanCoreMap (rightAdjointUnitToFullSpace C D w) ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore _).ι ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.RawAdjointUnitSpace C D) _).ι = _
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.kanCoreMap_ι]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
