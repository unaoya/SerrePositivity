module

public import SerrePositivity.InfinityCategories.F2.Presentable.Duality.RightUnitFiberReturn

/-!
概要：元の右射影の固定ファイバーと、可縮な固定右の随伴単位空間との同型。
方針：元の coslice 成分と両関手の射影を用いて、二つの回収射の往復を厳密に検証する。
規約：元の単位の全高次単体を保持し、同値の存在を仮定しない。
使われ方：元の右射影の各高次ファイバーの可縮性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Duality

/-- 概要：元の右ファイバーから単位空間へ送り戻す往復は恒等射。
方針：元の母空間への包含の単射性と、coslice 成分・左右の射影を計算する。
規約：単体集合の射の厳密な等式。
使われ方：右ファイバーの同型の順逆の一方。 -/
lemma rightUnitFiber_hom_inv_id (C D : PresentableInfinityObject.{u})
    (w : PrRMappingSpace D C _⦋0⦌) :
    rightFiberToAdjointUnitSpace C D w ≫ rightAdjointUnitToFiber C D w = 𝟙 _ := by
  apply vertexFiber_hom_ext (adjointUnitRight C D) w
  rw [Category.assoc, rightAdjointUnitToFiber_ι, Category.id_comp]
  apply (cancel_mono (adjointUnitUnderlying C D)).1
  rw [Category.assoc, rightAdjointUnitReturn_underlying]
  apply pullback.hom_ext
  · rw [Category.assoc, rightAdjointUnitRaw_unit, ← Category.assoc,
      rightFiberToAdjointUnitSpace_underlying, adjointUnitRightFiberToCoslice_unit]
    exact (Category.assoc (vertexFiberι (adjointUnitRight C D) w) (adjointUnitUnderlying C D)
      (pullback.fst _ (unitComposition C D))).symm
  · rw [Category.assoc, rightAdjointUnitRaw_base, comp_lift, SSet.comp_const,
      rightFiberToAdjointUnitSpace_left]
    calc
      _ = (vertexFiberι (adjointUnitRight C D) w ≫ adjointUnitLeft C D) ≫
          CartesianMonoidalCategory.lift (𝟙 (PrLMappingSpace C D)) (SSet.const w) := by
        rw [comp_lift, Category.comp_id, SSet.comp_const]
      _ = _ := by simpa only [Category.assoc] using (adjointUnitRightFiber_base C D w).symm

/-- 概要：固定右の単位空間から元のファイバーへ送り戻す往復は恒等射。
方針：元の coslice への包含の単射性と、実単位・左関手の回収の等式を計算する。
規約：元の単位の全単体上の厳密な等式。
使われ方：右ファイバーの同型の順逆の他方。 -/
lemma rightUnitFiber_inv_hom_id (C D : PresentableInfinityObject.{u})
    (w : PrRMappingSpace D C _⦋0⦌) :
    rightAdjointUnitToFiber C D w ≫ rightFiberToAdjointUnitSpace C D w = 𝟙 _ := by
  apply (cancel_mono (rightAdjointUnitUnderlying C D w.val)).1
  rw [Category.assoc, rightFiberToAdjointUnitSpace_underlying, Category.id_comp]
  apply pullback.hom_ext
  · rw [Category.assoc, adjointUnitRightFiberToCoslice_unit, ← Category.assoc,
      rightAdjointUnitToFiber_ι, ← Category.assoc, rightAdjointUnitReturn_underlying,
      rightAdjointUnitRaw_unit]
  · rw [Category.assoc, adjointUnitRightFiberToCoslice_left, ← Category.assoc,
      rightAdjointUnitToFiber_ι, ← Category.assoc, rightAdjointUnitReturn_left,
      rightAdjointUnitLeft_ι]
    rfl

/-- 概要：元の右射影の各固定ファイバーは固定右の随伴単位空間と厳密に同型。
方針：元の単位と左関手を保つ両方向の回収と、射影で検証した往復をまとめる。
規約：元の e1 の右写像空間の頂点を固定する。
使われ方：元の右射影の高次ファイバーの可縮性の移送。 -/
def rightUnitFiberIso (C D : PresentableInfinityObject.{u})
    (w : PrRMappingSpace D C _⦋0⦌) :
    vertexFiber (adjointUnitRight C D) w ≅ _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.RightAdjointUnitSpace C D w.val where
  hom := rightFiberToAdjointUnitSpace C D w
  inv := rightAdjointUnitToFiber C D w
  hom_inv_id := rightUnitFiber_hom_inv_id C D w
  inv_hom_id := rightUnitFiber_inv_hom_id C D w

/-- 概要：元の随伴単位の右射影の各固定ファイバーは可縮な Kan 複体。
方針：同じ実単位を保つ固定右単位空間との同型で可縮性を移す。
規約：全高次ファイバーの可縮性であり、射影の同値性は別に検証する。
使われ方：右射影の QCat 同値性の高次一意性側。 -/
lemma adjointUnitRightFiber_isContractibleKan (C D : PresentableInfinityObject.{u})
    (w : PrRMappingSpace D C _⦋0⦌) :
    IsContractibleKan (vertexFiber (adjointUnitRight C D) w) :=
  isContractibleKan_of_iso (rightUnitFiberIso C D w).symm
    (_root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.rightAdjointUnitSpace_isContractibleKan C D w.val)

end SerrePositivity.InfinityCategories.F2.Presentable.Duality
