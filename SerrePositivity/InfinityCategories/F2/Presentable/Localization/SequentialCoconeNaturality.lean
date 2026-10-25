module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.SequentialCoconeExtension

/-!
概要：次段階の全余錐の明示式と、前置図式の制限との自然性を証明する。
方針：二重 coslice の二度の uncurry と join 結合同型の自然性を使う。
規約：比較は全余錐の射の厳密な等号。
使われ方：HTT 5.5.4.13 の再帰で、選んだ側の全前置図式も元の表示に一致させる。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization
open HomotopyLimits
variable {K C : SSet.{u}} {p : K ⟶ C} {w z : JoinCocone p}
  (k : (sliceUnder p).Edge w z)

/-- 次段階の全余錐は、元の余錐間の辺を uncurry して join の括弧を戻すもの。 -/
lemma sequentialCoconeExtension_val :
    (sequentialCoconeExtension k).val =
      (stableJoinAssociator K Δ[0] Δ[0]).hom ≫
        joinMap (𝟙 K) (joinStdSimplexIso 0 0).hom ≫
          sliceUnderUncurry (SSet.yonedaEquiv.symm k.edge) := by
  let d := sequentialCoconeExtension k
  have hn := ConcreteCategory.congr_hom
    (NatTrans.congr_app (Iso.inv_hom_id (nestedCosliceIso w)) (Opposite.op ⦋0⦌))
    (edgeCosliceVertex k.toTruncated)
  change (nestedCosliceIso w).hom.app _ d = edgeCosliceVertex k.toTruncated at hn
  have h := nestedCosliceHomEquiv_doubleUncurry w (SSet.yonedaEquiv.symm d)
  rw [← nestedCosliceIso_hom_comp, SSet.yonedaEquiv_symm_comp,
    sliceUnderUncurry_yoneda, sliceUnderUncurry_yoneda, hn] at h
  change sliceUnderUncurry ((joinStdSimplexIso 0 0).hom ≫ SSet.yonedaEquiv.symm k.edge) =
    (stableJoinAssociator K Δ[0] Δ[0]).inv ≫ d.val at h
  rw [sliceUnderUncurry_precomp] at h
  have h' := congrArg (fun a ↦ (stableJoinAssociator K Δ[0] Δ[0]).hom ≫ a) h
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using h'.symm

/-- 次段階の全余錐を前置形状へ制限する操作は、元の辺を制限してから作る操作と一致する。 -/
lemma sequentialCoconeExtension_restrict_naturality {L : SSet.{u}} (i : L ⟶ K) :
    joinMap (joinMap i (𝟙 Δ[0])) (𝟙 Δ[0]) ≫ (sequentialCoconeExtension k).val =
      (sequentialCoconeExtension (k.map (sliceUnderRestrict p i))).val := by
  rw [sequentialCoconeExtension_val, sequentialCoconeExtension_val]
  have he : SSet.yonedaEquiv.symm (k.map (sliceUnderRestrict p i)).edge =
      SSet.yonedaEquiv.symm k.edge ≫ sliceUnderRestrict p i :=
    (SSet.yonedaEquiv_symm_comp k.edge (sliceUnderRestrict p i)).symm
  rw [he, sliceUnderUncurry_restrict]
  rw [← Category.assoc (joinMap (joinMap i (𝟙 Δ[0])) (𝟙 Δ[0]))
    (stableJoinAssociator K Δ[0] Δ[0]).hom,
    stableJoinAssociator_naturality]
  simp only [joinMap_id, Category.assoc]
  have hm : joinMap i (𝟙 (join Δ[0] Δ[0])) ≫
      joinMap (𝟙 K) (joinStdSimplexIso 0 0).hom =
        joinMap (𝟙 L) (joinStdSimplexIso 0 0).hom ≫ joinMap i (𝟙 Δ[1]) := by
    rw [← joinMap_comp, ← joinMap_comp]
    simp only [Category.id_comp, Category.comp_id]
  simpa only [Category.assoc] using
    congrArg (fun f ↦ (stableJoinAssociator L Δ[0] Δ[0]).hom ≫ f ≫
      sliceUnderUncurry (SSet.yonedaEquiv.symm k.edge)) hm

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
