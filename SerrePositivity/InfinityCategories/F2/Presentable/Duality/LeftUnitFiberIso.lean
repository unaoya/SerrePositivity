module

public import SerrePositivity.InfinityCategories.F2.Presentable.Duality.LeftUnitFiberReturn

/-!
概要：元の左射影の固定ファイバーと、可縮な固定左の随伴単位空間との同型。
方針：元の coslice 成分と両関手の射影を用いて、二つの回収射の往復を厳密に検証する。
規約：元の単位の全高次単体を保持し、同値の存在を仮定しない。
使われ方：元の左射影の各高次ファイバーの可縮性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Duality

/-- 概要：元の左ファイバーから単位空間へ送り戻す往復は恒等射。
方針：元の母空間への包含の単射性と、coslice 成分・左右の射影を計算する。
規約：単体集合の射の厳密な等式。
使われ方：左ファイバーの同型の順逆の一方。 -/
lemma leftUnitFiber_hom_inv_id (C D : PresentableInfinityObject.{u})
    (w : PrLMappingSpace C D _⦋0⦌) :
    leftFiberToAdjointUnitSpace C D w ≫ leftAdjointUnitToFiber C D w = 𝟙 _ := by
  apply vertexFiber_hom_ext (adjointUnitLeft C D) w
  rw [Category.assoc, leftAdjointUnitToFiber_ι, Category.id_comp]
  apply (cancel_mono (adjointUnitUnderlying C D)).1
  rw [Category.assoc, leftAdjointUnitReturn_underlying]
  apply pullback.hom_ext
  · rw [Category.assoc, leftAdjointUnitRaw_unit, ← Category.assoc,
      leftFiberToAdjointUnitSpace_underlying, adjointUnitLeftFiberToCoslice_unit]
    exact (Category.assoc (vertexFiberι (adjointUnitLeft C D) w) (adjointUnitUnderlying C D)
      (pullback.fst _ (unitComposition C D))).symm
  · rw [Category.assoc, leftAdjointUnitRaw_base, comp_lift, SSet.comp_const,
      leftFiberToAdjointUnitSpace_right]
    calc
      _ = (vertexFiberι (adjointUnitLeft C D) w ≫ adjointUnitRight C D) ≫
          CartesianMonoidalCategory.lift (SSet.const w) (𝟙 (PrRMappingSpace D C)) := by
        rw [comp_lift, Category.comp_id, SSet.comp_const]
      _ = _ := by simpa only [Category.assoc] using (adjointUnitLeftFiber_base C D w).symm

/-- 概要：固定左の単位空間から元のファイバーへ送り戻す往復は恒等射。
方針：元の coslice への包含の単射性と、実単位・右関手の回収の等式を計算する。
規約：元の単位の全単体上の厳密な等式。
使われ方：左ファイバーの同型の順逆の他方。 -/
lemma leftUnitFiber_inv_hom_id (C D : PresentableInfinityObject.{u})
    (w : PrLMappingSpace C D _⦋0⦌) :
    leftAdjointUnitToFiber C D w ≫ leftFiberToAdjointUnitSpace C D w = 𝟙 _ := by
  apply (cancel_mono (leftAdjointUnitUnderlying C D w.val)).1
  rw [Category.assoc, leftFiberToAdjointUnitSpace_underlying, Category.id_comp]
  apply pullback.hom_ext
  · rw [Category.assoc, adjointUnitLeftFiberToCoslice_unit, ← Category.assoc,
      leftAdjointUnitToFiber_ι, ← Category.assoc, leftAdjointUnitReturn_underlying,
      leftAdjointUnitRaw_unit]
  · rw [Category.assoc, adjointUnitLeftFiberToCoslice_right, ← Category.assoc,
      leftAdjointUnitToFiber_ι, ← Category.assoc, leftAdjointUnitReturn_right,
      leftAdjointUnitRight_ι]
    rfl

/-- 概要：元の左射影の各固定ファイバーは固定左の随伴単位空間と厳密に同型。
方針：元の単位と右関手を保つ両方向の回収と、射影で検証した往復をまとめる。
規約：元の e1 の左写像空間の頂点を固定する。
使われ方：元の左射影の高次ファイバーの可縮性の移送。 -/
def leftUnitFiberIso (C D : PresentableInfinityObject.{u})
    (w : PrLMappingSpace C D _⦋0⦌) :
    vertexFiber (adjointUnitLeft C D) w ≅ LeftAdjointUnitSpace C D w.val where
  hom := leftFiberToAdjointUnitSpace C D w
  inv := leftAdjointUnitToFiber C D w
  hom_inv_id := leftUnitFiber_hom_inv_id C D w
  inv_hom_id := leftUnitFiber_inv_hom_id C D w

/-- 概要：元の随伴単位の左射影の各固定ファイバーは可縮な Kan 複体。
方針：同じ実単位を保つ固定左単位空間との同型で可縮性を移す。
規約：全高次ファイバーの可縮性であり、射影の同値性は別に検証する。
使われ方：左射影の QCat 同値性の高次一意性側。 -/
lemma adjointUnitLeftFiber_isContractibleKan (C D : PresentableInfinityObject.{u})
    (w : PrLMappingSpace C D _⦋0⦌) :
    IsContractibleKan (vertexFiber (adjointUnitLeft C D) w) :=
  isContractibleKan_of_iso (leftUnitFiberIso C D w).symm
    (leftAdjointUnitSpace_isContractibleKan C D w.val)

end SerrePositivity.InfinityCategories.F2.Presentable.Duality
