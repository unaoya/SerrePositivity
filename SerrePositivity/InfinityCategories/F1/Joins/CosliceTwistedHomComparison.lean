module

public import SerrePositivity.InfinityCategories.F1.TwistedArrow.HomSpace
public import SerrePositivity.InfinityCategories.F1.Joins.CosliceTwistedArrowMap
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FunctorFiber

/-!
概要：元の coslice fiber の写像空間から、両半分を固定した twisted arrow の写像空間への比較。
方針：全空間の錐の比較を実際の二つの端点の fiber へ厳密に制限する。
規約：比較の単射性と各次数での式を示すが、同値性はここで仮定も結論もしない。
使われ方：表現可能射影と twisted arrow の比較の各 fiber で残る主比較射。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 元の coslice fiber の錐を、左右を固定した join の写像空間へ送る実際の比較。 -/
def cosliceTwistedHomMap {C : SSet.{u}} (x y : C _⦋0⦌) :
    vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm x)) y ⟶
      twistedArrowHomSpace x y :=
  vertexFiberLift (twistedArrowProjection C) (SSet.opObjEquiv.symm x, y)
    (vertexFiberι (sliceUnderProjection (SSet.yonedaEquiv.symm x)) y ≫
      cosliceTwistedArrowMap (SSet.yonedaEquiv.symm x)) (by
        apply CartesianMonoidalCategory.hom_ext
        · simp only [Category.assoc, twistedArrowProjection_fst, cosliceTwistedArrowMap_left,
            SSet.comp_const, SSet.const_comp, Equiv.apply_symm_apply]
          rfl
        · simp only [Category.assoc, twistedArrowProjection_snd, cosliceTwistedArrowMap_right,
            vertexFiberι_comp, SSet.const_comp]
          rfl)

/-- 比較を元の全空間へ含めると、同じ coslice の錐の比較を回収する。 -/
lemma cosliceTwistedHomMap_ι {C : SSet.{u}} (x y : C _⦋0⦌) :
    cosliceTwistedHomMap x y ≫ vertexFiberι (twistedArrowProjection C)
      (SSet.opObjEquiv.symm x, y) =
    vertexFiberι (sliceUnderProjection (SSet.yonedaEquiv.symm x)) y ≫
      cosliceTwistedArrowMap (SSet.yonedaEquiv.symm x) := rfl

/-- 各次数での実際の比較は、元の錐の左の重みを一点へ潰した合成。 -/
lemma cosliceTwistedHomMap_app_val {C : SSet.{u}} (x y : C _⦋0⦌) (n : ℕ)
    (s : (vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm x)) y) _⦋n⦌) :
    ((cosliceTwistedHomMap x y).app (Opposite.op ⦋n⦌) s).val =
      cosliceEdgewiseCollapse ⦋n⦌ ≫ s.val.val := rfl

/-- 比較は元の coslice fiber の単体を区別する。 -/
instance cosliceTwistedHomMap_mono {C : SSet.{u}} (x y : C _⦋0⦌) :
    Mono (cosliceTwistedHomMap x y) :=
  mono_of_mono_fac (cosliceTwistedHomMap_ι x y)

end SerrePositivity.InfinityCategories
