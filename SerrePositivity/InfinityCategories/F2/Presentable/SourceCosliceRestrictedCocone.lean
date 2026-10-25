module

public import SerrePositivity.InfinityCategories.F2.Presentable.SourceCosliceFilteredColimits
public import SerrePositivity.InfinityCategories.F2.Presentable.CofinalColimitExistence

/-!
概要：元の余錐を固定した始域からの射の全図式に制限し、同じ終域余錐を持つ coslice 余錐を作る。
方針：元の余錐を uncurry 図式へ制限し、反復 coslice の同型で戻す。
規約：底の余錐との比較は全 join 図式の等式。
使われ方：元の filtered 表示を、指定された途中段からの表示へ持ち上げる。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits

private lemma simplicialIso_inv_hom_apply {X Y : SSet.{u}} (e : X ≅ Y)
    (n : SimplexCategoryᵒᵖ) (y : Y.obj n) : e.hom.app n (e.inv.app n y) = y := by
  exact ConcreteCategory.congr_hom (NatTrans.congr_app e.inv_hom_id n) y

/-- 概要：固定始域からの図式上に、元の指定余錐から余錐を作る。
方針：展開した図式の余錐を反復 coslice 同型で戻す。
規約：元の余錐 c を使い、新たな余極限を選ばない。
使われ方：指定表示段からの相対余錐。 -/
def sourceCosliceRestrictedCocone {K A I C : SSet.{u}}
    (a : K ⟶ I) (s : A ⟶ sliceUnder a) (D : I ⟶ C) (c : JoinCocone D) :
    JoinCocone (s ≫ sliceUnderPostcomp a D) := by
  let b := s ≫ sliceUnderPostcomp a D
  have hU : sliceUnderUncurry b = sliceUnderUncurry s ≫ D :=
    sliceUnderUncurry_postcomp s D
  let d : (sliceUnder (sliceUnderUncurry b)) _⦋0⦌ :=
    (eqToIso (congrArg sliceUnder hU.symm)).hom.app (Opposite.op ⦋0⦌)
      (c.restrict (sliceUnderUncurry s))
  exact (iteratedSliceUnderIso b).inv.app (Opposite.op ⦋0⦌) d

/-- 概要：固定始域上に構成した余錐の底は、元の全余錐を終域図式に制限したもの。
方針：反復 coslice 同型の右制限の等式を各余錐に適用する。
規約：頂点・脚だけでなく全余錐値の等式。
使われ方：元の余極限性を指定した始域上の余錐へ移す。 -/
lemma sourceCosliceRestrictedCocone_projection {K A I C : SSet.{u}}
    (a : K ⟶ I) (s : A ⟶ sliceUnder a) (D : I ⟶ C) (c : JoinCocone D) :
    (mapJoinCocone (sliceUnderProjection (a ≫ D))
      (sourceCosliceRestrictedCocone a s D c)).val =
      (c.restrict (s ≫ sliceUnderProjection a)).val := by
  let b := s ≫ sliceUnderPostcomp a D
  have hU : sliceUnderUncurry b = sliceUnderUncurry s ≫ D :=
    sliceUnderUncurry_postcomp s D
  let d : (sliceUnder (sliceUnderUncurry b)) _⦋0⦌ :=
    (eqToIso (congrArg sliceUnder hU.symm)).hom.app (Opposite.op ⦋0⦌)
      (c.restrict (sliceUnderUncurry s))
  let v := (iteratedSliceUnderIso b).inv.app (Opposite.op ⦋0⦌) d
  have hv : (sliceUnderPostcomp b (sliceUnderProjection (a ≫ D))).app
      (Opposite.op ⦋0⦌) v =
      (Localization.uncurriedSourceRightRestriction b).app (Opposite.op ⦋0⦌) d := by
    rw [← Localization.iteratedSliceUnderIso_sourceRightRestriction b]
    change (Localization.uncurriedSourceRightRestriction b).app _
      ((iteratedSliceUnderIso b).hom.app _ ((iteratedSliceUnderIso b).inv.app _ d)) = _
    exact congrArg (fun z : (sliceUnder (sliceUnderUncurry b)) _⦋0⦌ ↦
      (Localization.uncurriedSourceRightRestriction b).app (Opposite.op ⦋0⦌) z)
      (simplicialIso_inv_hom_apply (iteratedSliceUnderIso b) (Opposite.op ⦋0⦌) d)
  change ((sliceUnderPostcomp b (sliceUnderProjection (a ≫ D))).app _ v).val = _
  rw [hv]
  change ((eqToIso (congrArg sliceUnder (sliceUnderUncurry_projection b))).hom.app
    (Opposite.op ⦋0⦌) ((sliceUnderRestrict (sliceUnderUncurry b) (joinInr K A)).app
      (Opposite.op ⦋0⦌) d)).val = _
  rw [Ind.sliceUnder_eqToIso_val (sliceUnderUncurry_projection b)]
  have hd : d.val = (c.restrict (sliceUnderUncurry s)).val :=
    Ind.sliceUnder_eqToIso_val hU.symm _
  change joinMap (joinInr K A) (𝟙 Δ[0]) ≫ d.val = _
  rw [hd]
  change joinMap (joinInr K A) (𝟙 Δ[0]) ≫
    (joinMap (sliceUnderUncurry s) (𝟙 Δ[0]) ≫ c.val) = _
  rw [← Category.assoc, ← joinMap_comp, Category.id_comp, sliceUnderUncurry_projection]
  rfl

end SerrePositivity.InfinityCategories.F2.Presentable
