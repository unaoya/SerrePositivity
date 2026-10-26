module

public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.StableInputLifting
public import SerrePositivity.InfinityCategories.F2.Presentable.PullbackCoconeCandidates
public import SerrePositivity.InfinityCategories.F2.Presentable.PullbackCosliceComparison

/-!
概要：固定入力と標的を保つ厳密に整合した二成分を元の引き戻しへ貼る。
方針：全余錐族を両成分の coslice の引き戻しへ貼り、既存の全 coslice 同型で戻す。
規約：元の入力図式と標的を全単体上で保持する。
使われ方：同値持ち上げ後の compact 成分対の全余錐の回収。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback

variable {E D B K : SSet.{u + 1}} (p : E ⟶ B) (q : D ⟶ B)
  (a : K ⟶ pullback p q) (z : JoinCocone a)

local notation "aE" => a ≫ pullback.fst p q
local notation "aD" => a ≫ pullback.snd p q
local notation "aB" => (a ≫ pullback.fst p q) ≫ p
local notation "zE" => mapJoinCocone (pullback.fst p q) z
local notation "zD" => mapJoinCocone (pullback.snd p q) z
local notation "zB" => mapJoinCocone p (mapJoinCocone (pullback.fst p q) z)

/-- 概要：厳密に整合した入力付き二成分は元の引き戻しの同じ入力上の頂点を与える。
方針：元の全二点余錐族を両 coslice の実引き戻しに貼る。
規約：両成分の全単体値を厳密に回収する。
使われ方：compact 成分対の比較同型を同値持ち上げで厳密化した後の貼り合わせ。 -/
lemma exists_inputPullbackSliceVertex_of_strict_components
    (hQ : aD ≫ q = aB) (hZ : (zD).val ≫ q = (zB).val)
    (cE : (sliceOver ((SSet.yonedaEquiv (X := sliceUnder aE)).symm zE)) _⦋0⦌)
    (cD : (sliceOver ((SSet.yonedaEquiv (X := sliceUnder aD)).symm zD)) _⦋0⦌)
    (h : (stableInputPostcomp aE p aB rfl zE zB rfl).app (Opposite.op ⦋0⦌) cE =
      (stableInputPostcomp aD q aB hQ zD zB hZ).app (Opposite.op ⦋0⦌) cD) :
    ∃ v : (sliceOver ((SSet.yonedaEquiv (X := sliceUnder a)).symm z)) _⦋0⦌,
      v.val ≫ sliceUnderPostcomp a (pullback.fst p q) = cE.val ∧
      v.val ≫ sliceUnderPostcomp a (pullback.snd p q) = cD.val := by
  have hraw := congrArg
    (fun σ : (sliceOver ((SSet.yonedaEquiv (X := sliceUnder aB)).symm zB)) _⦋0⦌ ↦ σ.val) h
  rw [stableInputPostcomp_val, stableInputPostcomp_val] at hraw
  have hP : stableCoslicePostcomp aE p aB rfl = sliceUnderPostcomp aE p := by
    simp only [stableCoslicePostcomp, eqToHom_refl, Category.comp_id]
  have hQ' : stableCoslicePostcomp aD q aB hQ = pullbackCoconeBaseMap p q a := rfl
  have hbase : pullbackCoconeBaseMap p q a = pullbackCosliceBaseMap p q a := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro σ
    apply Subtype.ext
    dsimp only [pullbackCoconeBaseMap, NatTrans.comp_app, types_comp_apply]
    exact Ind.sliceUnder_eqToIso_val hQ _
  rw [hP, hQ', hbase] at hraw
  let H := pullback.lift cE.val cD.val hraw
  let S := pullbackCosliceIso p q a
  let G := H ≫ S.inv
  have hSF : S.inv ≫ sliceUnderPostcomp a (pullback.fst p q) =
      pullback.fst (sliceUnderPostcomp aE p) (pullbackCosliceBaseMap p q a) := by
    rw [← pullbackCosliceIso_hom_fst p q a, ← Category.assoc,
      Iso.inv_hom_id, Category.id_comp]
  have hSD : S.inv ≫ sliceUnderPostcomp a (pullback.snd p q) =
      pullback.snd (sliceUnderPostcomp aE p) (pullbackCosliceBaseMap p q a) := by
    rw [← pullbackCosliceIso_hom_snd p q a, ← Category.assoc,
      Iso.inv_hom_id, Category.id_comp]
  have hGF : G ≫ sliceUnderPostcomp a (pullback.fst p q) = cE.val := by
    change (H ≫ S.inv) ≫ _ = _
    rw [Category.assoc, hSF]
    exact pullback.lift_fst _ _ _
  have hGD : G ≫ sliceUnderPostcomp a (pullback.snd p q) = cD.val := by
    change (H ≫ S.inv) ≫ _ = _
    rw [Category.assoc, hSD]
    exact pullback.lift_snd _ _ _
  have hfixed : joinInr Δ[0] Δ[0] ≫ G = (SSet.yonedaEquiv (X := sliceUnder a)).symm z := by
    apply sliceUnderUncurry_injective a
    rw [sliceUnderUncurry_yoneda]
    apply pullback.hom_ext
    · rw [← sliceUnderUncurry_postcomp, Category.assoc, hGF, cE.property,
        sliceUnderUncurry_yoneda]
      rfl
    · rw [← sliceUnderUncurry_postcomp, Category.assoc, hGD, cD.property,
        sliceUnderUncurry_yoneda]
      rfl
  exact ⟨⟨G, hfixed⟩, hGF, hGD⟩

end SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback
