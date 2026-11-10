module

public import SerrePositivity.InfinityCategories.F2.Presentable.Duality.AdjointVertices

/-!
概要：選んだ随伴を e1 の反対方向の関手圏の頂点にし、往復を比較する。
方針：元の保存条件で全部分複体へ戻し、随伴の一意性で関手同型を得る。
規約：往復の比較は h Fun の同型であり、高次の整合性は別工程とする。
使われ方：全 ∞ 圏の双対性へ進む前の頂点上の検証。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Duality

/-- 概要：小余極限保存関手を e1 の左関手圏の頂点にする。
方針：零単体の自己射の一意性で全部分複体の所属を検査する。
規約：元の関手の頂点をそのまま使う。
使われ方：選んだ左随伴の頂点への回収。 -/
def leftFunctorVertex {C D : PresentableInfinityObject.{u}}
    (F : C.obj ⟶ D.obj) (hF : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits F) : PrLFunctorSpace C D _⦋0⦌ :=
  ⟨(functorVertexEquiv C.obj D.obj) F, by
    intro f
    have hf : f = 𝟙 _ := Subsingleton.elim _ _
    subst f
    simpa only [op_id, Functor.map_id_apply, Equiv.symm_apply_apply] using hF⟩

/-- 概要：accessible な小極限保存関手を e1 の右関手圏の頂点にする。
方針：同じ頂点の全部分複体への所属を検査する。
規約：accessibility と小極限保存を同時に保持する。
使われ方：選んだ右随伴の頂点への回収。 -/
def rightFunctorVertex {C D : PresentableInfinityObject.{u}}
    (F : C.obj ⟶ D.obj) (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessibleFunctor F ∧ PreservesSmallLimits F) :
    PrRFunctorSpace C D _⦋0⦌ :=
  ⟨(functorVertexEquiv C.obj D.obj) F, by
    intro f
    have hf : f = 𝟙 _ := Subsingleton.elim _ _
    subst f
    simpa only [op_id, Functor.map_id_apply, Equiv.symm_apply_apply] using hF⟩

/-- 概要：左関手圏の頂点の選んだ右随伴を右関手圏に戻す。
方針：d により回収した保存条件を使用する。
規約：C から D の関手に D から C の関手を対応させる。
使われ方：双対対応の頂点写像。 -/
def rightAdjointVertex {C D : PresentableInfinityObject.{u}}
    (v : PrLFunctorSpace C D _⦋0⦌) : PrRFunctorSpace D C _⦋0⦌ :=
  rightFunctorVertex (chosenRightAdjoint v) (chosenRightAdjoint_condition v)

/-- 概要：右関手圏の頂点の選んだ左随伴を左関手圏に戻す。
方針：左随伴の小余極限保存を使用する。
規約：元の関手と逆向きの関手になる。
使われ方：逆対応の頂点写像。 -/
def leftAdjointVertex {C D : PresentableInfinityObject.{u}}
    (v : PrRFunctorSpace C D _⦋0⦌) : PrLFunctorSpace D C _⦋0⦌ :=
  leftFunctorVertex (chosenLeftAdjoint v) (chosenLeftAdjoint_condition v)

/-- 概要：右随伴を選んでから左随伴を選ぶ往復は元の左関手と同型。
方針：同じ右随伴に対する左随伴の一意性。
規約：h Fun 内の関手同型であり、頂点の等式に強めない。
使われ方：左側の往復比較。 -/
def leftRoundtripIso {C D : PresentableInfinityObject.{u}}
    (v : PrLFunctorSpace C D _⦋0⦌) :
    FunctorIso (chosenLeftAdjoint (rightAdjointVertex v)) (leftVertexFunctor v) := by
  have a : QCatAdjunction (chosenLeftAdjoint (rightAdjointVertex v))
      (chosenRightAdjoint v) := by
    simpa only [rightAdjointVertex, rightFunctorVertex, rightVertexFunctor,
      Equiv.symm_apply_apply] using chosenLeftAdjunction (rightAdjointVertex v)
  exact a.leftAdjointFunctorIso (chosenRightAdjunction v)

/-- 概要：左随伴を選んでから右随伴を選ぶ往復は元の右関手と同型。
方針：同じ左随伴に対する右随伴の一意性。
規約：全関手の h Fun 内の同型を返す。
使われ方：右側の往復比較。 -/
def rightRoundtripIso {C D : PresentableInfinityObject.{u}}
    (v : PrRFunctorSpace C D _⦋0⦌) :
    FunctorIso (chosenRightAdjoint (leftAdjointVertex v)) (rightVertexFunctor v) := by
  have a : QCatAdjunction (chosenLeftAdjoint v)
      (chosenRightAdjoint (leftAdjointVertex v)) := by
    simpa only [leftAdjointVertex, leftFunctorVertex, leftVertexFunctor,
      Equiv.symm_apply_apply] using chosenRightAdjunction (leftAdjointVertex v)
  exact a.rightAdjointFunctorIso (chosenLeftAdjunction v)

end SerrePositivity.InfinityCategories.F2.Presentable.Duality
