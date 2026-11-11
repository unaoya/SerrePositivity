module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.WeightedSectionTransform

/-!
概要：重み付き自然変換を切断の族へ写して戻す向きの逆関係。
方針：over 圏の射列は最後への標準の持ち上げを最後の構造射で後合成して復元できる。
規約：係数とパラメータの Kan 性は要求しない。
使われ方：Kerodon 5.3.3.1（Tag 025X）、7.5.3.12（Tag 03B1） の切断と重み付き end の対応。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
variable {I : Type u} [SmallCategory I] {A : SSet.{u}} {H : I ⥤ SSet.{u}}

/-- 概要：over 圏の射列は、底の全区間の標準持ち上げを最後の構造射で後合成して復元できる。
方針：対象の三角形の可換性と忘却関手の忠実性を使う。
規約：初区間の終点を最後の頂点に取る。
使われ方：Kerodon 5.3.3.1（Tag 025X）、7.5.3.12（Tag 03B1） の自然変換側の逆関係。 -/
lemma prefixOverChain_last_map {i : I} {n : ℕ} (σ : ComposableArrows (Over i) n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.prefixOverChain (σ ⋙ Over.forget i) (Fin.last n) ⋙
      Over.map (σ.obj (Fin.last n)).hom = σ := by
  refine CategoryTheory.Functor.ext (fun k => ?_) ?_
  · change Over.mk ((σ.map (homOfLE (Fin.le_last k))).left ≫
      (σ.obj (Fin.last n)).hom) = σ.obj k
    exact congrArg Over.mk (Over.w (σ.map (homOfLE (Fin.le_last k))))
  · intro k l f
    apply (Over.forget i).map_injective
    simp
    rfl

/-- 概要：自然変換から作った切断の係数を取り出すと元の係数の構成に一致する。
方針：構成した切断の底は定義で固定されるため、正規化の移送は恒等である。
規約：射影条件には標準の証明を使う。
使われ方：Kerodon 5.3.3.1（Tag 025X）、7.5.3.12（Tag 03B1） の自然変換側の逆関係。 -/
lemma weightedSectionCoefficients_fromTransform
    (η : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I ⊗ (Functor.const I).obj A ⟶ H)
    {n : ℕ} (σ : ComposableArrows I n) (a : A _⦋n⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedSectionCoefficients (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedNerveSectionFromTransform η)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedNerveSectionFromTransform_projection η) σ a =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveCoefficients η σ (SSet.yonedaEquiv.symm a) := rfl

/-- 概要：自然変換から作った切断を over 圏の射列で評価すると元の自然変換の評価になる。
方針：最後の構造射を自然変換の自然性で重み側へ移し、元の over 圏の射列を復元する。
規約：標準単体からの射の等式として述べる。
使われ方：Kerodon 5.3.3.1（Tag 025X）、7.5.3.12（Tag 03B1） の単体ごとの逆関係。 -/
lemma weightedSectionOverSimplex_fromTransform
    (η : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I ⊗ (Functor.const I).obj A ⟶ H)
    {i : I} {n : ℕ} (σ : ComposableArrows (Over i) n) (a : A _⦋n⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedSectionOverSimplex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedNerveSectionFromTransform η)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedNerveSectionFromTransform_projection η) σ a =
      lift ((SSet.yonedaEquiv (X := nerve (Over i))).symm σ) (SSet.yonedaEquiv.symm a) ≫
        η.app i := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedSectionOverSimplex
  rw [weightedSectionCoefficients_fromTransform]
  change (lift (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.prefixOverChain (σ ⋙ Over.forget i) (Fin.last n)))
    (stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion n n le_rfl) ≫ SSet.yonedaEquiv.symm a) ≫
      η.app (σ.obj (Fin.last n)).left) ≫ H.map (σ.obj (Fin.last n)).hom = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion_id, CategoryTheory.Functor.map_id, Category.id_comp, Category.assoc,
    ← η.naturality (σ.obj (Fin.last n)).hom]
  change lift (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.prefixOverChain (σ ⋙ Over.forget i) (Fin.last n)))
      (SSet.yonedaEquiv.symm a) ≫
    (((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I).map (σ.obj (Fin.last n)).hom ⊗ₘ 𝟙 A) ≫ η.app i) = _
  rw [← Category.assoc, lift_map, Category.comp_id]
  congr 2
  rw [SSet.yonedaEquiv_symm_comp]
  exact congrArg SSet.yonedaEquiv.symm (prefixOverChain_last_map σ)

/-- 概要：重み付き自然変換から切断の族を作って戻すと元の自然変換になる。
方針：各 over 圏の射列とパラメータの単体で評価し、Yoneda の自然性を使う。
規約：自然変換の厳密な等式であり、ホモトピーだけではない。
使われ方：Kerodon 5.3.3.1（Tag 025X）、7.5.3.12（Tag 03B1） の切断と重み付き end の対応の一方の逆関係。 -/
lemma weightedSectionTransform_fromTransform
    (η : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I ⊗ (Functor.const I).obj A ⟶ H) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedSectionTransform (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedNerveSectionFromTransform η)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedNerveSectionFromTransform_projection η) = η := by
  apply NatTrans.ext
  funext i
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨σ, a⟩
  change SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedSectionOverSimplex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedNerveSectionFromTransform η)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedNerveSectionFromTransform_projection η) σ a) =
      (η.app i).app (Opposite.op ⦋n⦌) (σ, a)
  rw [weightedSectionOverSimplex_fromTransform, SSet.yonedaEquiv_comp]
  congr 1
  apply Prod.ext
  · change (fst (nerve (Over i)) A).app (Opposite.op ⦋n⦌)
      (SSet.yonedaEquiv (lift (SSet.yonedaEquiv.symm σ) (SSet.yonedaEquiv.symm a))) = σ
    rw [← SSet.yonedaEquiv_comp, lift_fst, Equiv.apply_symm_apply]
  · change (snd (nerve (Over i)) A).app (Opposite.op ⦋n⦌)
      (SSet.yonedaEquiv (lift (SSet.yonedaEquiv.symm σ) (SSet.yonedaEquiv.symm a))) = a
    rw [← SSet.yonedaEquiv_comp, lift_snd, Equiv.apply_symm_apply]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
