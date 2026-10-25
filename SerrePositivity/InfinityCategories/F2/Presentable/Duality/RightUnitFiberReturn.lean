module

public import SerrePositivity.InfinityCategories.F2.Presentable.Duality.RightUnitReturnCondition

/-!
概要：固定右単位空間から元の固定右ファイバーへの逆射と、その射影の計算。
方針：同じ右頂点への定値性で fiber へ持ち上げ、元の左右の射影を回収する。
規約：元の写像空間と単位を全次数で保持する。
使われ方：固定右ファイバーと可縮な単位空間の厳密な同型。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Duality

instance leftMappingInclusion_mono (C D : PresentableInfinityObject.{u}) :
    Mono (leftMappingInclusion C D) := by
  dsimp only [leftMappingInclusion]
  infer_instance

instance adjointUnitUnderlying_mono (C D : PresentableInfinityObject.{u}) :
    Mono (adjointUnitUnderlying C D) := by
  dsimp only [adjointUnitUnderlying]
  infer_instance

instance rightAdjointUnitUnderlying_mono (C D : PresentableInfinityObject.{u})
    (w : PrRFunctorSpace D C _⦋0⦌) : Mono (rightAdjointUnitUnderlying C D w) := by
  dsimp only [rightAdjointUnitUnderlying]
  infer_instance

/-- 概要：元の右ファイバーからの比較は元の左写像空間への射影を保つ。
方針：全関手圏への包含の単射性を使い、両比較の左射影を照合する。
規約：元の Pr^L 写像空間上の厳密な等式。
使われ方：右ファイバー上の往復の第二射影の検証。 -/
lemma rightFiberToAdjointUnitSpace_left (C D : PresentableInfinityObject.{u})
    (w : PrRMappingSpace D C _⦋0⦌) :
    rightFiberToAdjointUnitSpace C D w ≫ rightAdjointUnitLeft C D w.val =
      vertexFiberι (adjointUnitRight C D) w ≫ adjointUnitLeft C D := by
  apply (cancel_mono (leftMappingInclusion C D)).1
  rw [Category.assoc, rightAdjointUnitLeft_ι]
  change rightFiberToAdjointUnitSpace C D w ≫ rightAdjointUnitUnderlying C D w.val ≫
    pullback.snd _ ((ihom C.obj).map (rightVertexFunctor w.val)) = _
  rw [← Category.assoc, rightFiberToAdjointUnitSpace_underlying,
    adjointUnitRightFiberToCoslice_left]
  exact (Category.assoc _ _ _).symm

/-- 概要：固定右単位から元の対応への逆射は元の左射影を回収する。
方針：母空間での第二射影を計算し、その第一成分を取る。
規約：元の左写像空間上の厳密な等式。
使われ方：固定右単位空間上の往復の検証。 -/
lemma rightAdjointUnitReturn_left (C D : PresentableInfinityObject.{u})
    (w : PrRMappingSpace D C _⦋0⦌) :
    rightAdjointUnitReturn C D w ≫ adjointUnitLeft C D = rightAdjointUnitLeft C D w.val := by
  change rightAdjointUnitReturn C D w ≫ adjointUnitUnderlying C D ≫
    pullback.snd _ (unitComposition C D) ≫ fst _ _ = _
  rw [← Category.assoc, rightAdjointUnitReturn_underlying,
    ← Category.assoc, rightAdjointUnitRaw_base, lift_fst]

/-- 概要：固定右単位から元の対応への逆射の右成分は元の右頂点に定値。
方針：母空間での第二射影を計算し、その第二成分を取る。
規約：同じ元の右頂点に対する全次数の定値性。
使われ方：元の固定右ファイバーへの逆射の持ち上げ。 -/
lemma rightAdjointUnitReturn_right (C D : PresentableInfinityObject.{u})
    (w : PrRMappingSpace D C _⦋0⦌) :
    rightAdjointUnitReturn C D w ≫ adjointUnitRight C D = SSet.const w := by
  change rightAdjointUnitReturn C D w ≫ adjointUnitUnderlying C D ≫
    pullback.snd _ (unitComposition C D) ≫ snd _ _ = _
  rw [← Category.assoc, rightAdjointUnitReturn_underlying,
    ← Category.assoc, rightAdjointUnitRaw_base, lift_snd]

/-- 概要：固定右単位空間から元の右射影の固定ファイバーへ戻す逆射。
方針：元の対応への回収を同じ右頂点上の fiber に持ち上げる。
規約：元の e1 の右写像空間の頂点を固定する。
使われ方：右ファイバーと可縮な固定右単位空間の同型の逆方向。 -/
def rightAdjointUnitToFiber (C D : PresentableInfinityObject.{u})
    (w : PrRMappingSpace D C _⦋0⦌) :
    RightAdjointUnitSpace C D w.val ⟶ vertexFiber (adjointUnitRight C D) w :=
  vertexFiberLift (adjointUnitRight C D) w (rightAdjointUnitReturn C D w)
    (rightAdjointUnitReturn_right C D w)

/-- 概要：固定右ファイバーへの逆射を元へ含めると同じ単位の回収射。
方針：fiber の持ち上げと包含の公式を使う。
規約：元の全高次単体を保持する。
使われ方：往復の射を元の対応空間で検証する。 -/
lemma rightAdjointUnitToFiber_ι (C D : PresentableInfinityObject.{u})
    (w : PrRMappingSpace D C _⦋0⦌) :
    rightAdjointUnitToFiber C D w ≫ vertexFiberι (adjointUnitRight C D) w =
      rightAdjointUnitReturn C D w :=
  vertexFiberLift_ι _ _ _ _

end SerrePositivity.InfinityCategories.F2.Presentable.Duality
