module

public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.RelativeAlternatingFactorization

/-!
概要：相対因子化の比較辺から、指定成分の全 slice 余錐を回収する。
方針：三因子 join の自然性と元の表示脚の二重 uncurry を使う。
規約：頂点だけでなく元の全単体の等式を返す。
使われ方：交互構成の一段延長における成分図式の整合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback
open HomotopyLimits

/-- 概要：相対因子化の slice 余錐を指定成分へ制限すると、同じ表示の延長になる。
方針：比較辺の厳密な制限を二重 uncurry の等式へ移す。
規約：元の表示添字と固定対象への全増大図式を保つ。
使われ方：次の閉前置段の指定成分の等式。 -/
lemma RelativeAlternatingFactorization.component_slice
    {κ : Cardinal.{u}} {B : SSet.{u + 1}}
    {x : (Δ[0] : SSet.{u + 1}) ⟶ B} {I : Fin 2 → SSet.{u}}
    {P : ∀ c, (SSet.uliftFunctor.{u + 1, u}).obj (I c) ⟶ sliceOver x}
    {a : AlternatingIndex κ} {s : RelativeAlternatingOpenStage κ x I P a}
    {c : Fin 2} (t : RelativeAlternatingFactorization s c) :
    joinMap ((SSet.uliftFunctor.{u + 1, u}).map
        (nerveMap (alternatingLowerSection κ a c))) (𝟙 Δ[0]) ≫
        (relativeSliceCocone s.diagram t.comparison).val =
      (((uliftSliceUnderIso.{u, u + 1} (s.index c)).hom.app (Opposite.op ⦋0⦌))
        (ULift.up t.index)).val ≫ P c := by
  let i := (SSet.uliftFunctor.{u + 1, u}).map
    (nerveMap (alternatingLowerSection κ a c))
  apply sliceOverUncurry_injective x
  rw [sliceOverUncurry_precomp, sliceOverUncurry_precomp]
  change joinMap (joinMap i (𝟙 Δ[0])) (𝟙 Δ[0]) ≫
      sliceOverUncurry (sliceOverCurry (relativeSliceCoconeMap s.diagram t.comparison)
        (relativeSliceCoconeMap_right s.diagram t.comparison)) = _
  rw [sliceOverUncurry_curry, relativeSliceCoconeMap]
  rw [← Category.assoc, joinAssociator_naturality]
  simp only [Category.assoc]
  rw [← Category.assoc (joinMap i _), ← joinMap_comp, Category.comp_id,
    joinMap_id, Category.id_comp, sliceUnderUncurry_yoneda]
  have he : joinMap i (𝟙 Δ[1]) ≫ t.comparison.edge.val =
      (Compact.coconeTransportLeg (sourceCosliceRestrictedCocone
        ((SSet.uliftFunctor.{u + 1, u}).map (s.index c))
        (uliftSliceUnderIso.{u, u + 1} (s.index c)).hom
        (P c ≫ sliceOverProjection x) (sliceDiagramCocone (P c)))
          (ULift.up t.index)).edge.val := t.component_edge
  have hn : joinMap i (joinStdSimplexIso 0 0).hom =
      joinMap (𝟙 _) (joinStdSimplexIso 0 0).hom ≫ joinMap i (𝟙 Δ[1]) := by
    rw [← joinMap_comp, Category.id_comp, Category.comp_id]
  rw [hn, Category.assoc, he]
  simpa only [sliceUnderUncurry_yoneda, sliceDiagramCocone] using
    sourceCosliceRestrictedCocone_leg_uncurry
      ((SSet.uliftFunctor.{u + 1, u}).map (s.index c))
      (uliftSliceUnderIso.{u, u + 1} (s.index c)).hom
      (P c ≫ sliceOverProjection x) (sliceDiagramCocone (P c)) (ULift.up t.index)

end SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback
