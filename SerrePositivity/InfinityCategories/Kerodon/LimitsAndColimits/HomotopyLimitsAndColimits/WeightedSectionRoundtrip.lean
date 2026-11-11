module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.WeightedSectionTransformRetraction

/-!
概要：weighted nerve の切断の族と Bousfield–Kan 重みの自然変換の厳密な対応。
方針：初区間の最後で切断を評価すると、その初区間の係数を回収できることを使う。
規約：任意のパラメータと係数図式を扱い、Kan 性は仮定しない。
使われ方：Kerodon 5.3.3.1（Tag 025X）、7.5.3.12（Tag 03B1） の重み付き end の切断模型。

対応節は Kerodon 7.5（Tag 039Y）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
variable {I : Type u} [SmallCategory I] {A : SSet.{u}} {H : I ⥤ SSet.{u}}

private lemma yoneda_lift {X Y : SSet.{u}} {n : ℕ} (x : X _⦋n⦌) (y : Y _⦋n⦌) :
    SSet.yonedaEquiv (lift (SSet.yonedaEquiv.symm x) (SSet.yonedaEquiv.symm y)) = (x, y) := by
  apply Prod.ext
  · change (fst X Y).app (Opposite.op ⦋n⦌)
      (SSet.yonedaEquiv (lift (SSet.yonedaEquiv.symm x) (SSet.yonedaEquiv.symm y))) = x
    rw [← SSet.yonedaEquiv_comp, lift_fst, Equiv.apply_symm_apply]
  · change (snd X Y).app (Opposite.op ⦋n⦌)
      (SSet.yonedaEquiv (lift (SSet.yonedaEquiv.symm x) (SSet.yonedaEquiv.symm y))) = y
    rw [← SSet.yonedaEquiv_comp, lift_snd, Equiv.apply_symm_apply]

/-- 概要：切断から作った自然変換の標準単体での評価は元の終点評価である。
方針：Yoneda で単体へ戻し、直積の標準単体を二つの単体の組として計算する。
規約：over 圏の射列とパラメータの単体を同時に評価する。
使われ方：Kerodon 5.3.3.1（Tag 025X）、7.5.3.12（Tag 03B1） の切断側の逆関係。 -/
lemma weightedSectionTransform_yoneda (s : nerve I ⊗ A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve H)
    (hs : s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection H = fst (nerve I) A)
    {i : I} {n : ℕ} (σ : ComposableArrows (Over i) n) (a : A _⦋n⦌) :
    lift ((SSet.yonedaEquiv (X := nerve (Over i))).symm σ) (SSet.yonedaEquiv.symm a) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedSectionTransform s hs).app i = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedSectionOverSimplex s hs σ a := by
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp, yoneda_lift]
  rfl

/-- 概要：初区間の over 圏の射列での終点評価は元の切断の対応する係数を回収する。
方針：切断の制限の公式を初区間の包含に適用し、最後の恒等射を消去する。
規約：初区間のパラメータも同じ包含で制限する。
使われ方：Kerodon 5.3.3.1（Tag 025X）、7.5.3.12（Tag 03B1） の元の係数の復元。 -/
lemma weightedSectionOverSimplex_prefix (s : nerve I ⊗ A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve H)
    (hs : s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection H = fst (nerve I) A)
    {n : ℕ} (σ : ComposableArrows I n) (a : A _⦋n⦌) (i : Fin (n + 1)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedSectionOverSimplex s hs (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.prefixOverChain σ i)
        (A.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion i.val n (Nat.le_of_lt_succ i.isLt)).op a) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedSectionCoefficients s hs σ a).app i := by
  let β := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion i.val n (Nat.le_of_lt_succ i.isLt)
  have hc := NatTrans.congr_app
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedSectionCoefficients_restriction s hs β σ a) (Fin.last i.val)
  have hb : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixRestriction β (Fin.last i.val) = 𝟙 ⦋i.val⦌ := by
    apply SimplexCategory.Hom.ext
    rfl
  let c : (Δ[i.val] : SSet.{u}) ⟶ H.obj (σ.obj i) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedSectionCoefficients s hs ((SimplexCategory.toCat.map β).toFunctor ⋙ σ)
      (A.map β.op a)).app (Fin.last i.val)
  change c ≫ H.map (σ.map (𝟙 i)) = _
  have hid : H.map (σ.map (𝟙 i)) = 𝟙 (H.obj (σ.obj i)) := by
    rw [σ.map_id, H.map_id]
  calc
    _ = c := by rw [hid, Category.comp_id]
    _ = stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixRestriction β (Fin.last i.val)) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedSectionCoefficients s hs σ a).app i := hc
    _ = _ := by
      have hm : stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixRestriction β (Fin.last i.val)) =
          𝟙 (Δ[i.val] : SSet.{u}) := by
        exact (congrArg (fun f : ⦋i.val⦌ ⟶ ⦋i.val⦌ => stdSimplex.map f) hb).trans
          (CategoryTheory.Functor.map_id stdSimplex _)
      exact (congrArg (fun f : (Δ[i.val] : SSet.{u}) ⟶ Δ[i.val] =>
        f ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedSectionCoefficients s hs σ a).app i) hm).trans (Category.id_comp _)

/-- 概要：切断から作った自然変換の係数は元の切断の全初区間の係数に一致する。
方針：各初区間で自然変換を標準単体に沿って評価し、元の係数を回収する公式を使う。
規約：係数の厳密な等式であり、全ての初区間を同時に比較する。
使われ方：Kerodon 5.3.3.1（Tag 025X）、7.5.3.12（Tag 03B1） の切断側の逆関係の係数部分。 -/
lemma weightedNerveCoefficients_fromSection (s : nerve I ⊗ A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve H)
    (hs : s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection H = fst (nerve I) A)
    {n : ℕ} (σ : ComposableArrows I n) (a : A _⦋n⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveCoefficients (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedSectionTransform s hs) σ (SSet.yonedaEquiv.symm a) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedSectionCoefficients s hs σ a := by
  apply NatTrans.ext
  funext i
  change lift (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.prefixOverChain σ i))
      (stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion i.val n (Nat.le_of_lt_succ i.isLt)) ≫
        SSet.yonedaEquiv.symm a) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedSectionTransform s hs).app (σ.obj i) = _
  have hy := SSet.yonedaEquiv_symm_naturality_left (X := A)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion i.val n (Nat.le_of_lt_succ i.isLt)) a
  rw [hy]
  exact (weightedSectionTransform_yoneda s hs (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.prefixOverChain σ i)
    (A.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion i.val n (Nat.le_of_lt_succ i.isLt)).op a)).trans
      (weightedSectionOverSimplex_prefix s hs σ a i)

/-- 概要：weighted nerve の切断の族を自然変換へ移して作り直すと元の切断になる。
方針：各単体で底と全初区間の係数を比較する。
規約：底上の実際の射の厳密な等式である。
使われ方：Kerodon 5.3.3.1（Tag 025X）、7.5.3.12（Tag 03B1） の切断側の逆関係。 -/
lemma weightedNerveSectionFromTransform_fromSection (s : nerve I ⊗ A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve H)
    (hs : s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection H = fst (nerve I) A) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedNerveSectionFromTransform (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedSectionTransform s hs) = s := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨σ, a⟩
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedSection_app s hs σ a]
  change (⟨σ, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveCoefficients (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedSectionTransform s hs) σ
    (SSet.yonedaEquiv.symm a)⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplex H n) = _
  rw [weightedNerveCoefficients_fromSection]

/-- 概要：Bousfield–Kan 重みの自然変換と weighted nerve の切断の族は厳密に対応する。
方針：両構成と二つの逆関係を全単射へまとめる。
規約：パラメータと係数図式の Kan 性は不要。
使われ方：Kerodon 7.5.3.12（Tag 03B1）、7.5.4.6（Tag 03BB） の重み付き end と切断模型の比較。 -/
noncomputable def weightedNerveSectionEquiv (H : I ⥤ SSet.{u}) (A : SSet.{u}) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I ⊗ (Functor.const I).obj A ⟶ H) ≃
      {s : nerve I ⊗ A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve H //
        s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection H = fst (nerve I) A} where
  toFun η := ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedNerveSectionFromTransform η,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedNerveSectionFromTransform_projection η⟩
  invFun s := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedSectionTransform s.val s.property
  left_inv η := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedSectionTransform_fromTransform η
  right_inv s := Subtype.ext (weightedNerveSectionFromTransform_fromSection s.val s.property)

/-- 概要：Bousfield–Kan 重み付き end への射と weighted nerve の切断の族は全単射で対応する。
方針：重み付き end の普遍性と、自然変換と切断の両逆関係を合成する。
規約：任意のパラメータ A を扱うが、単体集合の模型の同型は別途構成する。
使われ方：Kerodon 7.5.3.12（Tag 03B1）、7.5.4.6（Tag 03BB） の切断空間との比較の普遍性。 -/
noncomputable def bousfieldKanSectionHomEquiv (H : I ⥤ SSet.{u}) (A : SSet.{u}) :
    (A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim H) ≃
      {s : nerve I ⊗ A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve H //
        s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection H = fst (nerve I) A} :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsHomEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) H A).trans (weightedNerveSectionEquiv H A)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
