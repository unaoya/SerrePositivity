module

public import SerrePositivity.InfinityCategories.HA.Monads.OppositeOrdinalActionMapProfiles
public import SerrePositivity.InfinityCategories.HA.Monads.IntervalMixedBalancing

/-!
概要：実区間同値の逆と二つの混合合成の全射を有限区間の射で照合する。
方針：厳密な往復の関手等式を回収へ移し、既存の実随伴の一意性を使う。
規約：選択された原像の定義を推測せず、全射の等式で検収する。
使われ方：HA Proposition 4.7.3.3、Riehl–Verity Remark 3.3.8 の全水平結合則。
Kerodon Remark 6.2.1.4（Tag 02EN）。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory Opposite MonoidalCategory

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：区間圏への全関手の等式は有限単調射の表示を保つ。
方針：同じ関手へ戻す。規約：全ての添字圏の射。
使われ方：Riehl–Verity Remark 3.3.8 の逆区間表示の自然性の移送。 -/
lemma intervalOrderHom_functor_map_heq {I : Type u} [Category.{v} I]
    {F G : I ⥤ IntervalSimplexCategory} (h : F = G) {X Y : I} (f : X ⟶ Y) :
    HEq (F.map f).hom.toOrderHom (G.map f).hom.toOrderHom := by
  cases h
  rfl

/-- 概要：実区間同値の逆の全射は元の区間射の回収である。
方針：実際の往復の関手等式を回収へ移し、区間表示・回収の相互逆性を使う。
規約：原像の選択の実装へ仮定を足さない。使われ方：Riehl–Verity Remark 3.3.8 のirの逆。 -/
lemma ordinalIntervalInverse_map_heq {X Y : IntervalSimplexCategory} (f : X ⟶ Y) :
    HEq (augmentedOrderHom (ordinalIntervalEquivalence.inverse.map f).unop)
      (ordinalRecoverMap f.hom.toOrderHom f.property.1 f.property.2) := by
  let a := augmentedOrderHom (ordinalIntervalEquivalence.inverse.map f).unop
  have h := intervalOrderHom_functor_map_heq ordinalInterval_target_roundtrip
    (X := X) (Y := Y) f
  change HEq (ordinalIntervalMap a) f.hom.toOrderHom at h
  have hr := ordinalRecoverMap_heq (ordinalInterval_inverse_card X) (ordinalInterval_inverse_card Y)
    (ordinalIntervalMap_zero a) (ordinalIntervalMap_last a) f.property.1 f.property.2 h
  exact (heq_of_eq (ordinalRecoverMap_interval a)).symm.trans hr

/-- 概要：全増大順序和の区間表示は二つの区間表示の端点共有。
方針：全順序和の射の比較を区間表示へ移し、実際の区間表示の積の法則を使う。
規約：空も含む全射を比較する。使われ方：Riehl–Verity Remark 3.3.8 の反対側の自己Hom。 -/
lemma augmentedInterval_tensor_heq {A B C D : AugmentedSimplexCategory}
    (f : A ⟶ B) (g : C ⟶ D) :
    HEq (ordinalIntervalMap (augmentedOrderHom (f ⊗ₘ g)))
      (ordinalGlue (ordinalIntervalMap (augmentedOrderHom f))
        (ordinalIntervalMap (augmentedOrderHom g))) := by
  have h := ordinalIntervalMap_heq (augmentedOrdinalCard_tensor A C)
    (augmentedOrdinalCard_tensor B D) (augmentedOrderHom_tensor f g)
  exact h.trans (heq_of_eq (ordinalIntervalMap_append (augmentedOrderHom f) (augmentedOrderHom g)))

/-- 概要：最小元保存・最大元保存の混合合成の区間表示は元の二射の順序和。
方針：構成元の順序和に戻る全関手等式と、既存順序和の全射の照合を使う。
規約：忠実な区間表示の下の全射であり、元の射も回収できる。
使われ方：HA Proposition 4.7.3.3 の混合水平結合則。 -/
lemma mixedBottomTopInterval_map_heq {X₁ X₂ : BottomSimplexCategory}
    {Y₁ Y₂ : TopSimplexCategory} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) :
    HEq (ordinalIntervalMap (augmentedOrderHom
        (mixedBottomTopOrdinal.map (X := (X₁, Y₁)) (Y := (X₂, Y₂)) (f, g)).unop))
      (ordinalAppend f.hom.toOrderHom g.hom.toOrderHom) := by
  have h := intervalOrderHom_functor_map_heq mixedBottomTopOrdinal_representation
    (X := (X₁, Y₁)) (Y := (X₂, Y₂)) (f, g)
  change HEq (ordinalIntervalMap (augmentedOrderHom
      (mixedBottomTopOrdinal.map (X := (X₁, Y₁)) (Y := (X₂, Y₂)) (f, g)).unop))
    (AugmentedSimplexCategory.tensorHomOf f.hom g.hom).toOrderHom at h
  exact h.trans (simplexTensorHomOf_append_heq f.hom g.hom)

/-- 概要：逆順の混合合成の全射は最大元保存・最小元保存の端点共有。
方針：元の区間同値の逆を回収で照合し、実随伴の比較を使う。
規約：元の混合合成の射を変えない。使われ方：HA Proposition 4.7.3.3 の全水平結合則。 -/
lemma mixedTopBottomOrdinal_map_heq {X₁ X₂ : TopSimplexCategory}
    {Y₁ Y₂ : BottomSimplexCategory} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) :
    HEq (augmentedOrderHom
        (mixedTopBottomOrdinal.map (X := (X₁, Y₁)) (Y := (X₂, Y₂)) (f, g)))
      (ordinalGlue f.hom.toOrderHom g.hom.toOrderHom) := by
  let l := topSimplexLeftAdjoint f
  let r := bottomSimplexRightAdjoint g
  let h := bottomTopIntervalSum.map
    (X := ((⟨X₂.obj⟩ : BottomSimplexCategory), (⟨Y₂.obj⟩ : TopSimplexCategory)))
    (Y := ((⟨X₁.obj⟩ : BottomSimplexCategory), (⟨Y₁.obj⟩ : TopSimplexCategory))) (l, r)
  let k := ordinalAppendNonempty l.hom.toOrderHom r.hom.toOrderHom
  have hk : h.hom.toOrderHom = k := simplexTensorHomOf_append l.hom r.hom
  have hk₀ : k 0 = 0 := by
    rw [← hk]
    exact h.property.1
  have hk₁ : k (Fin.last (X₂.obj.len + Y₂.obj.len + 1)) =
      Fin.last (X₁.obj.len + Y₁.obj.len + 1) := by
    rw [← hk]
    exact h.property.2
  have hp := ordinalIntervalInverse_map_heq h
  have hr := ordinalRecoverMap_heq
    (a := X₂.obj.len + Y₂.obj.len + 1) (b := X₁.obj.len + Y₁.obj.len + 1)
    (c := X₂.obj.len + Y₂.obj.len + 1) (d := X₁.obj.len + Y₁.obj.len + 1)
    rfl rfl h.property.1 h.property.2 hk₀ hk₁ (heq_of_eq hk)
  change HEq (augmentedOrderHom (ordinalIntervalEquivalence.inverse.map h).unop)
    (ordinalGlue f.hom.toOrderHom g.hom.toOrderHom)
  exact hp.trans (hr.trans (heq_of_eq
    (ordinalRecoverMap_append_glue f.hom.toOrderHom g.hom.toOrderHom
      f.property g.property hk₀ hk₁)))

end SerrePositivity.InfinityCategories.HA.Monads
