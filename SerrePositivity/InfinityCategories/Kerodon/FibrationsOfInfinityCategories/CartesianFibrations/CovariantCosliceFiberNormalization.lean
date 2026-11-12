module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.PointSliceReversePinchedComparison

/-!
概要：共変表現可能値に現れる反転した fiber を、元の coslice fiber に正規化する。
方針：既存の反転 fiber 同型と二重反転の標準同型を合成する。
規約：元の fiber 同型と左 pinched 比較を保持する。
使われ方：G8 の表現可能値の同じ比較の自然性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories
open TheSliceAndJoinConstructions MorphismSpaces IsomorphismsAndIsofibrations

namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：元の左 pinched 模型を、元の単体集合の coslice fiber へ戻す同じ反転経路。
方針：右 fiber の反転、反転 slice の同型、二重反転の正規化を合成する。
規約：二重反転を定義的に消去しない。使われ方：表現可能値の比較の接続。 -/
def covariantCosliceFiberNormalization {C : SSet.{u}} (x y : C _⦋0⦌) :
    pinchedHomLeft x y ⟶ vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm x)) y :=
  SSet.opFunctor.map (pinchedHomToSliceFiber (X := C.op)
    (SSet.opObjEquiv.symm y) (SSet.opObjEquiv.symm x)) ≫
      (pointSliceReverseFiberIso (B := C.op)
        (SSet.opObjEquiv.symm x) (SSet.opObjEquiv.symm y)).hom ≫
          pointCosliceFiberMap (SSet.opFunctorCompOpFunctorIso.app C).hom
            (SSet.opObjEquiv.symm (SSet.opObjEquiv.symm x))
            (SSet.opObjEquiv.symm (SSet.opObjEquiv.symm y))

/-- 概要：元の反転経路で戻してから左 pinched 比較を行うと恒等射。
方針：左 pinched 比較の自然性と反転 fiber の座標の等式を使う。
規約：全次数の厳密な等式。使われ方：元の値比較の逆の正規化。 -/
lemma covariantCosliceFiberNormalization_hom {C : SSet.{u}} (x y : C _⦋0⦌) :
    covariantCosliceFiberNormalization x y ≫ (cosliceFiberPinchedLeftIso x y).hom =
      𝟙 (pinchedHomLeft x y) := by
  unfold covariantCosliceFiberNormalization
  simp only [Category.assoc]
  erw [PinchedLeftMap.cosliceFiberPinchedLeftIso_naturality]
  simp only [Category.assoc]
  erw [reassoc_of% (pointSliceReverseFiberIso_pinchedLeft (B := C.op)
    (SSet.opObjEquiv.symm y) (SSet.opObjEquiv.symm x))]
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  apply SSet.opObjEquiv.injective
  apply Basic.PinchedHom.Simplex.ext
  rfl

/-- 概要：同じ反転経路は、元の左 pinched 比較の指定逆そのもの。
方針：左 pinched 比較の順射を消去する。
規約：別の fiber 同型は選ばない。使われ方：正本の表現可能値との厳密な照合。 -/
lemma covariantCosliceFiberNormalization_eq_inv {C : SSet.{u}} (x y : C _⦋0⦌) :
    covariantCosliceFiberNormalization x y = (cosliceFiberPinchedLeftIso x y).inv := by
  apply (cancel_mono (cosliceFiberPinchedLeftIso x y).hom).mp
  rw [covariantCosliceFiberNormalization_hom, Iso.inv_hom_id]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
