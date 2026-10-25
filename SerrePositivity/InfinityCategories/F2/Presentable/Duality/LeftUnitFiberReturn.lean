module

public import SerrePositivity.InfinityCategories.F2.Presentable.Duality.LeftUnitReturnCondition
public import SerrePositivity.InfinityCategories.F2.Presentable.Duality.RightUnitFiberReturn

/-!
概要：固定左単位空間から元の固定左ファイバーへの逆射と、その射影の計算。
方針：同じ左頂点への定値性で fiber へ持ち上げ、元の左右の射影を回収する。
規約：元の写像空間と単位を全次数で保持する。
使われ方：固定左ファイバーと可縮な単位空間の厳密な同型。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Duality

instance rightMappingInclusion_mono (C D : PresentableInfinityObject.{u}) :
    Mono (rightMappingInclusion D C) := by
  dsimp only [rightMappingInclusion]
  infer_instance

instance leftAdjointUnitUnderlying_mono (C D : PresentableInfinityObject.{u})
    (w : PrLFunctorSpace C D _⦋0⦌) : Mono (leftAdjointUnitUnderlying C D w) := by
  dsimp only [leftAdjointUnitUnderlying]
  infer_instance

/-- 概要：元の左ファイバーからの比較は右写像空間への射影を保つ。
方針：全関手圏への包含の単射性で両比較の右射影を照合する。
規約：元の Pr^R 写像空間上の厳密な等式。
使われ方：左ファイバー上の往復の底の検証。 -/
lemma leftFiberToAdjointUnitSpace_right (C D : PresentableInfinityObject.{u})
    (w : PrLMappingSpace C D _⦋0⦌) :
    leftFiberToAdjointUnitSpace C D w ≫ leftAdjointUnitRight C D w.val =
      vertexFiberι (adjointUnitLeft C D) w ≫ adjointUnitRight C D := by
  apply (cancel_mono (rightMappingInclusion D C)).1
  rw [Category.assoc, leftAdjointUnitRight_ι]
  change leftFiberToAdjointUnitSpace C D w ≫ leftAdjointUnitUnderlying C D w.val ≫
    pullback.snd _ ((pre (leftVertexFunctor w.val)).app C.obj) = _
  rw [← Category.assoc, leftFiberToAdjointUnitSpace_underlying,
    adjointUnitLeftFiberToCoslice_right]
  exact (Category.assoc _ _ _).symm

/-- 概要：固定左単位から元の対応への逆射は右射影を回収する。
方針：母空間の底の第二成分を計算する。
規約：元の右写像空間上の厳密な等式。
使われ方：固定左単位空間上の往復の検証。 -/
lemma leftAdjointUnitReturn_right (C D : PresentableInfinityObject.{u})
    (w : PrLMappingSpace C D _⦋0⦌) :
    leftAdjointUnitReturn C D w ≫ adjointUnitRight C D = leftAdjointUnitRight C D w.val := by
  change leftAdjointUnitReturn C D w ≫ adjointUnitUnderlying C D ≫
    pullback.snd _ (unitComposition C D) ≫ snd _ _ = _
  rw [← Category.assoc, leftAdjointUnitReturn_underlying,
    ← Category.assoc, leftAdjointUnitRaw_base, lift_snd]

/-- 概要：固定左単位から元の対応への逆射の左成分は固定頂点に定値。
方針：母空間の底の第一成分を計算する。
規約：同じ元の左頂点に対する全次数の定値性。
使われ方：元の固定左ファイバーへの持ち上げ。 -/
lemma leftAdjointUnitReturn_left (C D : PresentableInfinityObject.{u})
    (w : PrLMappingSpace C D _⦋0⦌) :
    leftAdjointUnitReturn C D w ≫ adjointUnitLeft C D = SSet.const w := by
  change leftAdjointUnitReturn C D w ≫ adjointUnitUnderlying C D ≫
    pullback.snd _ (unitComposition C D) ≫ fst _ _ = _
  rw [← Category.assoc, leftAdjointUnitReturn_underlying,
    ← Category.assoc, leftAdjointUnitRaw_base, lift_fst]

/-- 概要：固定左単位空間から元の左射影の固定ファイバーへ戻す。
方針：元の対応への回収を同じ左頂点上の fiber に持ち上げる。
規約：元の e1 の左写像空間の頂点を固定する。
使われ方：左ファイバーと可縮単位空間の同型の逆射。 -/
def leftAdjointUnitToFiber (C D : PresentableInfinityObject.{u})
    (w : PrLMappingSpace C D _⦋0⦌) :
    LeftAdjointUnitSpace C D w.val ⟶ vertexFiber (adjointUnitLeft C D) w :=
  vertexFiberLift (adjointUnitLeft C D) w (leftAdjointUnitReturn C D w)
    (leftAdjointUnitReturn_left C D w)

/-- 概要：固定左ファイバーへの逆射を元へ含めると同じ単位の回収射。
方針：fiber の持ち上げと包含の公式を使う。
規約：元の全高次単体を保持する。
使われ方：往復の射を元の対応空間で検証する。 -/
lemma leftAdjointUnitToFiber_ι (C D : PresentableInfinityObject.{u})
    (w : PrLMappingSpace C D _⦋0⦌) :
    leftAdjointUnitToFiber C D w ≫ vertexFiberι (adjointUnitLeft C D) w =
      leftAdjointUnitReturn C D w :=
  vertexFiberLift_ι _ _ _ _

end SerrePositivity.InfinityCategories.F2.Presentable.Duality
