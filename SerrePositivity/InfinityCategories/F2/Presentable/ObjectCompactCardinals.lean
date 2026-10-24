module

public import SerrePositivity.InfinityCategories.F2.Presentable.IndCardinalChange
public import SerrePositivity.InfinityCategories.F2.Presentable.SmallPosetColimitCompact
public import SerrePositivity.InfinityCategories.F2.Ind.CofinalUniverseLift
public import SerrePositivity.InfinityCategories.F2.Ind.CofinalCoconeRestriction

/-!
概要：accessible 圏の小さい対象族に共通する compact 濃度を構成する。
方針：各対象の生成表示を小さい cofinal poset へ戻し、その濃度を超える正則濃度を取る。
規約：交換条件は実証済みの濃度変更条件から供給し、各対象の compact 性を仮定しない。
使われ方：随伴関手定理の accessible な Hom 族と右随伴の濃度調整。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：κ-accessible 圏の元の対象は任意の上限を超える濃度で compact。
方針：同じ対象の生成余極限を小さい poset に制限し、その全体を小さい余極限として評価する。
規約：元の対象を厳密に保持し、一般交換定理の追加仮定を要求しない。
使われ方：小さい対象族の共通 compact 濃度。 -/
lemma IsKappaAccessible.exists_compactCardinal {κ : Cardinal.{u}}
    {C : SSet.{u + 1}} [Quasicategory C] (hC : IsKappaAccessible κ C)
    (x : C _⦋0⦌) (σ : Cardinal.{u}) :
    ∃ μ : Cardinal.{u}, μ.IsRegular ∧ σ < μ ∧ Compact.IsKappaCompact.{u, u + 1} μ x := by
  obtain ⟨A, hA, i, hi⟩ := hC.2.2
  have := hA
  have : Fact κ.IsRegular := ⟨hC.1⟩
  obtain ⟨J, hJ, hκJ, a, c, hv, hc⟩ := hi.presentation x
  have := hJ
  have := hκJ
  obtain ⟨I, o, f, hI, _, hf⟩ := Ind.exists_cofinal_kappaFiltered_poset (κ := κ) J
  let := o
  have := hI
  let r := (SSet.uliftFunctor.{u + 1, u}).map f
  have hcr : IsColimitCone (c.restrict r) :=
    (Ind.isColimitCone_iff_restrict_rightCofinal r (Ind.isRightCofinal_ulift f hf) c).mp hc
  obtain ⟨μ, hμ, hσ, hb⟩ := exists_regular_cardinalChangeBound κ (max σ (Cardinal.mk I))
  have : Fact μ.IsRegular := ⟨hμ⟩
  have hIμ : HasCardinalLT I μ :=
    (hasCardinalLT_iff_cardinal_mk_lt I μ).mpr ((le_max_right _ _).trans_lt hσ)
  have hm : Compact.IsKappaCompact.{u, u + 1} μ (c.restrict r).vertex := by
    apply isMuCompact_smallPosetColimit_of_kappaCompact hb I hIμ (c.restrict r) hcr
    rintro ⟨j⟩
    exact hi.compact (a.app (Opposite.op ⦋0⦌) (f.app (Opposite.op ⦋0⦌) j))
  rw [JoinCocone.vertex_restrict, hv] at hm
  exact ⟨μ, hμ, (le_max_left _ _).trans_lt hσ, hm⟩

/-- 概要：accessible 圏の各対象は任意の指定上限を超える正則濃度で compact。
方針：元の accessibility の濃度を取り出して生成表示による定理を使う。
規約：presentable 性や全小余極限の存在は要求しない。
使われ方：Hom 関手の濃度調整。 -/
lemma IsAccessible.exists_compactCardinal {C : SSet.{u + 1}} [Quasicategory C]
    (hC : IsAccessible C) (x : C _⦋0⦌) (σ : Cardinal.{u}) :
    ∃ μ : Cardinal.{u}, μ.IsRegular ∧ σ < μ ∧ Compact.IsKappaCompact.{u, u + 1} μ x := by
  obtain ⟨κ, hκ⟩ := hC
  exact hκ.exists_compactCardinal x σ

/-- 概要：accessible 圏の小さい対象族は共通の正則濃度で全て compact。
方針：各対象の濃度を同じ宇宙で一括評価し、compact 性の単調性を使う。
規約：元の族の全対象と指定上限を保持する。
使われ方：随伴関手定理の小さい生成対象の像の共通評価。 -/
lemma IsAccessible.exists_common_compactCardinal {C : SSet.{u + 1}} [Quasicategory C]
    (hC : IsAccessible C) {ι : Type u} (x : ι → C _⦋0⦌) (σ : Cardinal.{u}) :
    ∃ μ : Cardinal.{u}, μ.IsRegular ∧ σ < μ ∧
      ∀ i, Compact.IsKappaCompact.{u, u + 1} μ (x i) := by
  let hs := fun i ↦ hC.exists_compactCardinal (x i) σ
  let κ : ι → Cardinal.{u} := fun i ↦ (hs i).choose
  obtain ⟨μ, hμ, hσ, hb⟩ := exists_regular_cardinalChangeBound_family κ σ
  exact ⟨μ, hμ, hσ, fun i ↦ ((hs i).choose_spec.2.2).of_le (hb i).le⟩

end SerrePositivity.InfinityCategories.F2.Presentable
