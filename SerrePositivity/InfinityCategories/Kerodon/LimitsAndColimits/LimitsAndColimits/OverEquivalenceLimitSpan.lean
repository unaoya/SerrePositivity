module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.OverEquivalenceLimitComposition

/-!
概要：既存の底上の極限比較の三因子から、中間極限錐の選択を消去する。
方針：前後の標準比較との合成則を使い、二つの中間同型を相殺する。
規約：HTT §1.2.13・Kerodon §7.1（Tag 02K2）の構成の法則。指定された同値を保つ。
使われ方：R04の元の分類図式比較の値の計算。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 指定した二つの中間同型で同じ三因子の比較を書き換えても、外端の同型は変わらない。 -/
private lemma iso_span_middle {C : Type u} [Category.{v} C] {x y s₁ s₂ t₁ t₂ : C}
    (a₁ : x ≅ s₁) (a₂ : x ≅ s₂) (m₁ : s₁ ≅ t₁) (m₂ : s₂ ≅ t₂)
    (c₁ : y ≅ t₁) (c₂ : y ≅ t₂) (s : s₁ ≅ s₂) (t : t₁ ≅ t₂)
    (ha : a₁ ≪≫ s = a₂) (hm : s ≪≫ m₂ = m₁ ≪≫ t) (hc : c₁ ≪≫ t = c₂) :
    a₁ ≪≫ m₁ ≪≫ c₁.symm = a₂ ≪≫ m₂ ≪≫ c₂.symm := by
  have hm' := congrArg Iso.hom hm
  simp only [Iso.trans_hom] at hm'
  subst a₂ c₂
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Category.assoc]
  rw [← Category.assoc s.hom m₂.hom, hm']
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

/-- 底上の指定同値に沿う三つの極限比較では、中間の指定極限錐は相殺する。
HTT §1.2.13・Kerodon §7.1（Tag 02K2）の既存の極限比較の合成則。 -/
@[cite HTT "1.2.13" (partial := special) "底上の同値による指定極限比較の三因子で中間極限を相殺する計算法則。"]
lemma limitVertexIsoOfOverEquivalence_span_middle
    {A B C D K X : SSet.{u}} [Quasicategory A] [Quasicategory B]
    [Quasicategory C] [Quasicategory D] [Quasicategory X]
    (a : A ⟶ B) (b : B ⟶ C) (c : D ⟶ C)
    (ha : IsQCatEquivalence a) (hb : IsQCatEquivalence b) (hc : IsQCatEquivalence c)
    {p : A ⟶ K} {q : B ⟶ K} {r : C ⟶ K} {s : D ⟶ K}
    (hwa : a ≫ q = p) (hwb : b ≫ r = q) (hwc : c ≫ r = s) (O : K ⟶ X)
    (c₀ : JoinCone (p ≫ O)) (d₀ : JoinCone (s ≫ O))
    (s₁ s₂ : JoinCone (q ≫ O)) (t₁ t₂ : JoinCone (r ≫ O))
    (hc₀ : IsLimitCone c₀) (hd₀ : IsLimitCone d₀)
    (hs₁ : IsLimitCone s₁) (hs₂ : IsLimitCone s₂)
    (ht₁ : IsLimitCone t₁) (ht₂ : IsLimitCone t₂) :
    limitVertexIsoOfOverEquivalence a ha hwa O c₀ s₁ hc₀ hs₁ ≪≫
      limitVertexIsoOfOverEquivalence b hb hwb O s₁ t₁ hs₁ ht₁ ≪≫
      (limitVertexIsoOfOverEquivalence c hc hwc O d₀ t₁ hd₀ ht₁).symm =
    limitVertexIsoOfOverEquivalence a ha hwa O c₀ s₂ hc₀ hs₂ ≪≫
      limitVertexIsoOfOverEquivalence b hb hwb O s₂ t₂ hs₂ ht₂ ≪≫
      (limitVertexIsoOfOverEquivalence c hc hwc O d₀ t₂ hd₀ ht₂).symm := by
  let a₁ := limitVertexIsoOfOverEquivalence a ha hwa O c₀ s₁ hc₀ hs₁
  let a₂ := limitVertexIsoOfOverEquivalence a ha hwa O c₀ s₂ hc₀ hs₂
  let m₁ := limitVertexIsoOfOverEquivalence b hb hwb O s₁ t₁ hs₁ ht₁
  let m₂ := limitVertexIsoOfOverEquivalence b hb hwb O s₂ t₂ hs₂ ht₂
  let c₁ := limitVertexIsoOfOverEquivalence c hc hwc O d₀ t₁ hd₀ ht₁
  let c₂ := limitVertexIsoOfOverEquivalence c hc hwc O d₀ t₂ hd₀ ht₂
  let es := limitVertexIso s₁ s₂ hs₁ hs₂
  let et := limitVertexIso t₁ t₂ ht₁ ht₂
  have heA : a₁ ≪≫ es = a₂ := by
    apply Iso.ext
    exact limitVertexIsoOfOverEquivalence_hom_comp a ha hwa O c₀ s₁ s₂ hc₀ hs₁ hs₂
  have heM : es ≪≫ m₂ = m₁ ≪≫ et := by
    apply Iso.ext
    exact (limitVertexIso_hom_comp_overEquivalence b hb hwb O s₁ s₂ t₂ hs₁ hs₂ ht₂).trans
      (limitVertexIsoOfOverEquivalence_hom_comp b hb hwb O s₁ t₁ t₂ hs₁ ht₁ ht₂).symm
  have heC : c₁ ≪≫ et = c₂ := by
    apply Iso.ext
    exact limitVertexIsoOfOverEquivalence_hom_comp c hc hwc O d₀ t₁ t₂ hd₀ ht₁ ht₂
  exact iso_span_middle a₁ a₂ m₁ m₂ c₁ c₂ es et heA heM heC

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
