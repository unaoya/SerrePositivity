module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.PointSliceReverseCoordinates
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedLeftMap

/-!
概要：元の反転 slice fiber の同型を、同じ左 pinched 模型の比較と照合する。
方針：既存の join の反転座標を単体の値へ戻す。
規約：二重反転を恒等と定義的に同一視しない。
使われ方：G8 の表現可能値の同じ比較の自然性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories
open TheSliceAndJoinConstructions MorphismSpaces FullFaithfulAndEssentiallySurjectiveFunctors

namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：元の右 pinched fiber の反転を左模型へ送る射は、標準二重反転の射の反転。
方針：join の逆反転の座標と左単体の座標を照合する。
規約：両端の表示と全次数を保持。使われ方：表現可能値の fiber 比較の正規化。 -/
lemma pointSliceReverseFiberIso_pinchedLeft {B : SSet.{u}} (x z : B _⦋0⦌) :
    SSet.opFunctor.map (pinchedHomToSliceFiber x z) ≫
      (pointSliceReverseFiberIso z x).hom ≫
        (cosliceFiberPinchedLeftIso (X := B.op)
          (SSet.opObjEquiv.symm z) (SSet.opObjEquiv.symm x)).hom =
      SSet.opFunctor.map (pinchedHomMap (SSet.opFunctorCompOpFunctorIso.app B).inv x z) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  apply SSet.opObjEquiv.injective
  apply Basic.PinchedHom.Simplex.ext
  apply SSet.opObjEquiv.injective
  change cosliceFiberSimplex n
      ((pointSliceReverseFiberIso z x).hom.app (Opposite.op ⦋n⦌)
        ((SSet.opFunctor.map (pinchedHomToSliceFiber x z)).app _ s)) = _
  unfold cosliceFiberSimplex
  rw [pointSliceReverseFiberIso_pinched_app_val, Iso.inv_hom_id_assoc]
  rw [stableReverseSimplex_yoneda, Equiv.apply_symm_apply]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
