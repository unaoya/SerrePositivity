module

public import SerrePositivity.InfinityCategories.F2.Presentable.SourceCosliceRestrictedCocone
public import SerrePositivity.InfinityCategories.F2.Presentable.SplitCoconeExtensionFaces
public import SerrePositivity.InfinityCategories.F2.Compact.CoconeLegEdge

/-!
概要：固定始域の下に移した元の余錐を、全二重 uncurry で回収する。
方針：反復 coslice 同型の逆を相殺し、元の全 join 制限へ戻す。
規約：全余錐の高次成分を保持する。
使われ方：交互図式の次の表示脚と元の増大余錐の整合。
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

private lemma iso_inv_hom_vertex {X Y : SSet.{u}} (e : X ≅ Y) (y : Y _⦋0⦌) :
    e.hom.app (Opposite.op ⦋0⦌) (e.inv.app (Opposite.op ⦋0⦌) y) = y :=
  ConcreteCategory.congr_hom (NatTrans.congr_app e.inv_hom_id (Opposite.op ⦋0⦌)) y

/-- 概要：相対表示余錐を二重展開すると元の全余錐の指定制限を厳密に回収する。
方針：同型の逆の相殺と固定図式の等号による移送の値を使う。
規約：余錐の全射の等式。
使われ方：元の表示余錐脚の全高次成分の回収。 -/
lemma sourceCosliceRestrictedCocone_uncurry {K A I C : SSet.{u}}
    (a : K ⟶ I) (s : A ⟶ sliceUnder a) (D : I ⟶ C) (c : JoinCocone D) :
    (joinAssociator K A Δ[0]).hom ≫
      sliceUnderUncurry (sourceCosliceRestrictedCocone a s D c).val =
      joinMap (sliceUnderUncurry s) (𝟙 Δ[0]) ≫ c.val := by
  let b := s ≫ sliceUnderPostcomp a D
  have hU : sliceUnderUncurry b = sliceUnderUncurry s ≫ D :=
    sliceUnderUncurry_postcomp s D
  let d : (sliceUnder (sliceUnderUncurry b)) _⦋0⦌ :=
    (eqToIso (congrArg sliceUnder hU.symm)).hom.app (Opposite.op ⦋0⦌)
      (c.restrict (sliceUnderUncurry s))
  have h := iteratedCocone_vertex_val b ((iteratedSliceUnderIso b).inv.app
    (Opposite.op ⦋0⦌) d)
  rw [iso_inv_hom_vertex] at h
  have hd : d.val = (c.restrict (sliceUnderUncurry s)).val :=
    Ind.sliceUnder_eqToIso_val hU.symm _
  exact h.symm.trans hd

/-- 概要：相対表示の元の脚を展開すると、元の余錐を対応する全後続余錐へ制限したもの。
方針：指定脚の全辺表示と二重 uncurry の比較を合成する。
規約：元の表示脚の全高次成分を保持する。
使われ方：次の交互増大余錐と元の表示増大余錐の整合。 -/
lemma sourceCosliceRestrictedCocone_leg_uncurry {K A I C : SSet.{u}}
    (a : K ⟶ I) (s : A ⟶ sliceUnder a) (D : I ⟶ C) (c : JoinCocone D)
    (j : A _⦋0⦌) :
    (joinAssociator K Δ[0] Δ[0]).hom ≫
      joinMap (𝟙 K) (joinStdSimplexIso 0 0).hom ≫
        sliceUnderUncurry (SSet.yonedaEquiv.symm
          (Compact.coconeTransportLeg (sourceCosliceRestrictedCocone a s D c) j).edge) =
      joinMap (s.app (Opposite.op ⦋0⦌) j).val (𝟙 Δ[0]) ≫ c.val := by
  let V := sourceCosliceRestrictedCocone a s D c
  have hleg : SSet.yonedaEquiv.symm (Compact.coconeTransportLeg V j).edge =
      (joinStdSimplexIso 0 0).inv ≫ joinMap (SSet.yonedaEquiv.symm j) (𝟙 Δ[0]) ≫ V.val := by
    rw [Compact.coconeTransportLeg_edge]
    exact Equiv.symm_apply_apply SSet.yonedaEquiv _
  rw [hleg, sliceUnderUncurry_precomp]
  rw [← Category.assoc (joinMap _ _), ← joinMap_comp, Iso.hom_inv_id,
    Category.id_comp, joinMap_id, Category.id_comp, sliceUnderUncurry_precomp]
  rw [← Category.assoc, ← joinAssociator_naturality, Category.assoc,
    sourceCosliceRestrictedCocone_uncurry]
  rw [← Category.assoc, ← joinMap_comp, Category.id_comp,
    ← sliceUnderUncurry_precomp, SSet.yonedaEquiv_symm_comp, sliceUnderUncurry_yoneda]

end SerrePositivity.InfinityCategories.F2.Presentable
