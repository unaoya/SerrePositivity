module

public import SerrePositivity.InfinityCategories.F2.Presentable.Duality.LeftUnitRawReturn

/-!
概要：固定左単位の母写像を元の随伴対応の固定左ファイバーへ持ち上げる。
方針：左右の関手と同じ単位辺の回収によって指定単位条件を移す。
規約：元の実単位を変えず、元の e1 の写像空間へ戻す。
使われ方：元の左ファイバーと可縮単位空間との同型の逆射。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Duality

/-- 概要：母空間へ戻した右関手は元の固定左単位の右関手。
方針：底の第二成分と右関手の回収を関手頂点の表示の逆へ移す。
規約：元の単体集合の射として等しい。
使われ方：戻した実単位の右端点の照合。 -/
lemma leftAdjointUnitRaw_rightFunctor (C D : PresentableInfinityObject.{u})
    (w : PrLMappingSpace C D _⦋0⦌) (x : LeftAdjointUnitSpace C D w.val _⦋0⦌) :
    unitRightFunctor ((leftAdjointUnitRaw C D w).app (Opposite.op ⦋0⦌) x) =
      leftUnitRightFunctor x.val.val := by
  have hb := congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) x) (leftAdjointUnitRaw_base C D w)
  have hl := congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) x) (leftAdjointUnitRight_ι C D w.val)
  exact congrArg (fun z ↦ (functorVertexEquiv D.obj C.obj).symm z)
    ((congrArg (fun z : (PrLMappingSpace C D ⊗ PrRMappingSpace D C) _⦋0⦌ ↦
      z.2.val.val) hb).trans hl)

/-- 概要：母空間へ戻した左関手は固定した元の左関手。
方針：底の第一成分を零次の定値写像の値で計算する。
規約：元の左関手の厳密な等式。
使われ方：戻した実単位の左端点の照合。 -/
lemma leftAdjointUnitRaw_leftFunctor (C D : PresentableInfinityObject.{u})
    (w : PrLMappingSpace C D _⦋0⦌) (x : LeftAdjointUnitSpace C D w.val _⦋0⦌) :
    unitLeftFunctor ((leftAdjointUnitRaw C D w).app (Opposite.op ⦋0⦌) x) =
      leftVertexFunctor w.val := by
  have hb := congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) x) (leftAdjointUnitRaw_base C D w)
  have hw : (SSet.const w : LeftAdjointUnitSpace C D w.val ⟶ PrLMappingSpace C D).app
      (Opposite.op ⦋0⦌) x = w := pinchedConstant_zero w
  exact (congrArg (fun z : (PrLMappingSpace C D ⊗ PrRMappingSpace D C) _⦋0⦌ ↦
    leftVertexFunctor z.1.val) hb).trans
      (congrArg (fun z : PrLMappingSpace C D _⦋0⦌ ↦ leftVertexFunctor z.val) hw)

/-- 概要：母空間へ戻した単位辺は元の固定左単位の辺。
方針：coslice 成分の保存を元の辺の回収へ移す。
規約：元の一次単体を変更しない。
使われ方：指定単位条件の同じ Hom 類を回収する。 -/
lemma leftAdjointUnitRaw_unitEdge (C D : PresentableInfinityObject.{u})
    (w : PrLMappingSpace C D _⦋0⦌) (x : LeftAdjointUnitSpace C D w.val _⦋0⦌) :
    (unitCorrespondenceEdge ((leftAdjointUnitRaw C D w).app (Opposite.op ⦋0⦌) x)).edge =
      (leftUnitEdge x.val.val).edge := by
  exact congrArg (fun s ↦ (sliceUnderVertexEdge (functorVertex (𝟙 C.obj)) s).edge)
    (congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) x) (leftAdjointUnitRaw_unit C D w))

/-- 概要：母空間へ戻した実単位は元の随伴単位の条件を満たす。
方針：左右の端点の回収と同じ単位辺の Hom 類で条件を移す。
規約：新たな随伴の存在や単位の選択を仮定しない。
使われ方：元の随伴単位の全部分空間への逆射の持ち上げ。 -/
lemma leftAdjointUnitRaw_unitCondition (C D : PresentableInfinityObject.{u})
    (w : PrLMappingSpace C D _⦋0⦌) (x : LeftAdjointUnitSpace C D w.val _⦋0⦌) :
    UnitMappingSpaceCondition
      (F := unitLeftFunctor ((leftAdjointUnitRaw C D w).app (Opposite.op ⦋0⦌) x))
      (G := unitRightFunctor ((leftAdjointUnitRaw C D w).app (Opposite.op ⦋0⦌) x))
      (unitCorrespondenceHom ((leftAdjointUnitRaw C D w).app (Opposite.op ⦋0⦌) x)) := by
  have he := edgeHom_heq
    (unitCorrespondenceEdge ((leftAdjointUnitRaw C D w).app (Opposite.op ⦋0⦌) x))
    (leftUnitEdge x.val.val) (leftAdjointUnitRaw_unitEdge C D w x)
  exact (unitCondition_transport (leftAdjointUnitRaw_leftFunctor C D w x)
    (leftAdjointUnitRaw_rightFunctor C D w x) _ _ he).mpr
      (fullSubcomplexOnVertices_vertex x.val)

/-- 概要：固定左の単位空間から元の随伴単位条件の全部分複体へ戻す。
方針：元の実単位の母写像を同じ指定単位条件で持ち上げる。
規約：元の単位の全単体を保持する。
使われ方：元の随伴対応への逆射の構成。 -/
def leftAdjointUnitToFullSpace (C D : PresentableInfinityObject.{u})
    (w : PrLMappingSpace C D _⦋0⦌) : LeftAdjointUnitSpace C D w.val ⟶
    (fullSubcomplexOnVertices (RawAdjointUnitSpace C D)
      (fun v ↦ UnitMappingSpaceCondition (unitCorrespondenceHom v)) : SSet.{u + 1}) :=
  fullSubcomplexLift _ (leftAdjointUnitRaw C D w) (leftAdjointUnitRaw_unitCondition C D w)

/-- 概要：固定左の単位空間から元の随伴単位の core へ戻す。
方針：Kan 始域から元の全部分空間の core へ持ち上げる。
規約：元の実単位の対応空間を標的とする。
使われ方：元の左ファイバーへの逆射の構成。 -/
def leftAdjointUnitReturn (C D : PresentableInfinityObject.{u})
    (w : PrLMappingSpace C D _⦋0⦌) :
    LeftAdjointUnitSpace C D w.val ⟶ AdjointUnitMappingSpace C D :=
  kanCoreMap (leftAdjointUnitToFullSpace C D w)

/-- 概要：元の対応へ戻した射を母空間へ含めると同じ実単位の母写像。
方針：core と全部分複体の包含を順に相殺する。
規約：全次数の射の厳密な等式。
使われ方：固定左条件と往復の射の検証。 -/
lemma leftAdjointUnitReturn_underlying (C D : PresentableInfinityObject.{u})
    (w : PrLMappingSpace C D _⦋0⦌) :
    leftAdjointUnitReturn C D w ≫ adjointUnitUnderlying C D = leftAdjointUnitRaw C D w := by
  change kanCoreMap (leftAdjointUnitToFullSpace C D w) ≫
    (quasicategoryCore _).ι ≫ (fullSubcomplexOnVertices (RawAdjointUnitSpace C D) _).ι = _
  rw [← Category.assoc, kanCoreMap_ι]
  exact fullSubcomplexLift_ι _ _ _

end SerrePositivity.InfinityCategories.F2.Presentable.Duality
