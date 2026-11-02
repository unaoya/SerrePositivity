module

public import SerrePositivity.InfinityCategories.F2.Presentable.PiSmallQuasicategory
public import SerrePositivity.InfinityCategories.Stable.Filtered.KappaFilteredCoslices
public import SerrePositivity.InfinityCategories.Core.InnerPullback
public import SerrePositivity.InfinityCategories.F1B.Cofinality.QuillenA

/-!
概要：同じ宇宙の filtered な族を一つの filtered 添字へ揃える。
方針：成分ごとの余錐を組み立て、射影の coslice 引き戻しでも同じ構成を使う。
規約：添字族の濃度制限や宇宙の持ち上げを要求しない。
使われ方：P-10、辺族の余積表示の共通添字。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：同じ宇宙の κ-filtered 圏の任意の積も κ-filtered。
方針：指定図式の各成分で選んだ全余錐を直積へまとめる。
規約：添字族は κ 未満とは限らない。
使われ方：共通 filtered 添字の構成。 -/
instance piSSetSmall_isKappaFiltered {κ : Cardinal.{u}} {B : Type u}
    (J : B → SSet.{u}) [∀ b, Quasicategory (J b)] [∀ b, IsKappaFiltered κ (J b)] :
    IsKappaFiltered κ (piSSetSmall J) where
  cocone_nonempty hK f := by
    classical
    let c := fun b ↦ Classical.choice
      (IsKappaFiltered.cocone_nonempty hK (f ≫ piSSetSmallProjection J b))
    refine ⟨⟨piSSetSmallLift (fun b ↦ (c b).val), ?_⟩⟩
    apply piSSetSmall_hom_ext
    intro b
    simpa only [Category.assoc, piSSetSmallLift_projection] using (c b).property

/-- 概要：積射影の基底変更も、元の各因子と変更先が κ-filtered なら κ-filtered。
方針：指定成分は変更先の余錐で固定し、残りの成分の余錐だけを選ぶ。
規約：引き戻し全体の quasicategory 性を明示入力とする。
使われ方：積射影の coslice の filtered 性。 -/
lemma piSSetSmallProjection_pullback_isKappaFiltered {κ : Cardinal.{u}} {B : Type u}
    (J : B → SSet.{u}) [∀ b, Quasicategory (J b)] [∀ b, IsKappaFiltered κ (J b)]
    (b : B) {Q : SSet.{u}} [Quasicategory Q] [IsKappaFiltered κ Q] (q : Q ⟶ J b)
    [Quasicategory (pullback (piSSetSmallProjection J b) q)] :
    IsKappaFiltered κ (pullback (piSSetSmallProjection J b) q) where
  cocone_nonempty hK f := by
    classical
    let p := piSSetSmallProjection J b
    obtain ⟨d⟩ := IsKappaFiltered.cocone_nonempty hK (f ≫ pullback.snd p q)
    have hb : joinInl _ Δ[0] ≫ (d.val ≫ q) =
        f ≫ pullback.fst p q ≫ piSSetSmallProjection J b := by
      rw [← Category.assoc, d.property, Category.assoc, pullback.condition]
    have hc (i : B) : ∃ c : JoinCocone (f ≫ pullback.fst p q ≫ piSSetSmallProjection J i),
        i = b → HEq c.val (d.val ≫ q) := by
      by_cases h : i = b
      · subst i
        exact ⟨⟨d.val ≫ q, hb⟩, fun _ ↦ HEq.rfl⟩
      · obtain ⟨c⟩ := IsKappaFiltered.cocone_nonempty hK
          (f ≫ pullback.fst p q ≫ piSSetSmallProjection J i)
        exact ⟨c, fun hi ↦ (h hi).elim⟩
    choose c hc using hc
    let g := piSSetSmallLift (fun i ↦ (c i).val)
    have hg : g ≫ p = d.val ≫ q := eq_of_heq (hc b rfl)
    refine ⟨⟨pullback.lift g d.val hg, ?_⟩⟩
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst]
      apply piSSetSmall_hom_ext
      intro i
      simpa only [Category.assoc, piSSetSmallLift_projection, g] using (c i).property
    · simpa only [Category.assoc, pullback.lift_snd] using d.property

/-- 概要：同じ宇宙の正則 κ-filtered 圏の積の各射影は right cofinal。
方針：各 coslice の引き戻しを κ-filtered と示し、弱可縮性から Quillen A を使う。
規約：κ は正則、因子の個数には制限を課さない。
使われ方：複数の表示を同じ小さい filtered 添字へ揃える。 -/
lemma piSSetSmallProjection_isRightCofinal {κ : Cardinal.{u}} [Fact κ.IsRegular]
    {B : Type u} (J : B → SSet.{u}) [∀ b, Quasicategory (J b)]
    [∀ b, IsKappaFiltered κ (J b)] (b : B) :
    IsRightCofinal (piSSetSmallProjection J b) := by
  apply isRightCofinal_of_weaklyContractible_coslices
  intro x
  let a : Δ[0] ⟶ J b := SSet.yonedaEquiv.symm x
  have hκ : κ.IsRegular := Fact.out
  have : IsKappaFiltered κ (sliceUnder a) := isKappaFiltered_sliceUnder hκ
    (isKappaSmall_of_finite hκ.aleph0_le _) a
  have : IsKappaFiltered κ
      (pullback (piSSetSmallProjection J b) (sliceUnderProjection a)) :=
    piSSetSmallProjection_pullback_isKappaFiltered J b _
  have := isFilteredInfinity_of_isKappaFiltered hκ.aleph0_le
    (pullback (piSSetSmallProjection J b) (sliceUnderProjection a))
  exact isWeaklyContractible_of_isFilteredInfinity _

/-- 概要：同じ宇宙の任意の κ-filtered 族は、全因子へ共終な共通 κ-filtered 添字を持つ。
方針：元の直積とその全射影を返す。
規約：正則 κ と各因子の κ-filtered 性だけを使う。
使われ方：P-f の小さい辺族の余積表示を同期する公開入口。 -/
lemma exists_common_kappaFiltered_cofinal_index {κ : Cardinal.{u}} [Fact κ.IsRegular]
    {B : Type u} (J : B → SSet.{u}) [∀ b, Quasicategory (J b)]
    [∀ b, IsKappaFiltered κ (J b)] :
    ∃ (K : SSet.{u}) (hK : Quasicategory K), letI := hK
      IsKappaFiltered κ K ∧ ∃ p : ∀ b, K ⟶ J b, ∀ b, IsRightCofinal (p b) := by
  exact ⟨piSSetSmall J, inferInstance, inferInstance, piSSetSmallProjection J,
    piSSetSmallProjection_isRightCofinal (κ := κ) J⟩

end SerrePositivity.InfinityCategories.F2.Presentable
