module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PrecompositionUnderCriterion
public import Mathlib.CategoryTheory.Comma.Over.Pullback

/-!
概要：固定された基底からの単射の図式の pushout による同値の保存。
方針：単射の同値条件の cobase change と相対写像円柱による保存判定を合わせる。
規約：固定基底から二対象への包含は単射とする。
使われ方：Kerodon §4.6.2（Tag 01HM） の固定境界を持つ図式の貼り合わせ。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：単射であり前合成の同値条件を満たす射のクラス。
方針：二つの既存の条件を合わせる。
規約：新しい同値の定義ではなく、貼り合わせの補助クラス。
使われ方：Kerodon §4.6.2（Tag 01HM） の cobase change の検査。 -/
def monoPrecompositionEquivalences : MorphismProperty SSet.{u} :=
  fun _ _ f ↦ Mono f ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence f

/-- 概要：単射の前合成の同値条件は cobase change で保存される。
方針：adhesive 性の単射保存と検証済みの同値条件の pushout 保存を合わせる。
規約：相手側の貼り合わせ射は任意。
使われ方：Kerodon §4.6.2（Tag 01HM） の under 圏の pushout 関手。 -/
instance monoPrecompositionEquivalences_isStableUnderCobaseChange :
    monoPrecompositionEquivalences.{u}.IsStableUnderCobaseChange where
  of_isPushout h hf := by
    have := hf.1
    exact ⟨Adhesive.mono_of_isPushout_of_mono_left h.flip, hf.2.of_isPushout h.flip⟩

/-- 概要：固定基底の単射の図式間の同値は pushout により保存される。
方針：pushout 関手の単射の同値保存を相対写像円柱の判定で全ての射に広げる。
規約：X と Y の固定基底からの射は単射。g と f.right の単射性は不要。
使われ方：Kerodon §4.6.2（Tag 01HM） の固定境界を持つ貼り合わせ。 -/
lemma isPrecompositionEquivalence_underPushout_map {A C : SSet.{u}} (g : A ⟶ C)
    {X Y : Under A} [Mono X.hom] [Mono Y.hom] (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence f.right) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (((Under.pushout g).map f).right) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_map_under_of_mono
    (Under.pushout g ⋙ Under.forget C) ?_ f hf
  intro X Y _ _ k _ hk
  exact (monoPrecompositionEquivalences.underPushoutMap g k ⟨inferInstance, hk⟩).2

/-- 概要：基底を固定した二つの pushout の比較は、貼る対象間の同値を保存する。
方針：選択された pushout への同型を通じて under 圏の補題に移す。
規約：基底から二つの貼る対象への射は単射。比較射の単射性は不要。
使われ方：Kerodon §4.6.2（Tag 01HM） の境界を固定したセルの貼り合わせ。 -/
lemma isPrecompositionEquivalence_of_pushout_fixed_base {A B B' C D D' : SSet.{u}}
    {i : A ⟶ B} {i' : A ⟶ B'} [Mono i] [Mono i'] {g : A ⟶ C}
    {r : B ⟶ D} {s : C ⟶ D} {r' : B' ⟶ D'} {s' : C ⟶ D'}
    (hP : IsPushout i g r s) (hP' : IsPushout i' g r' s')
    (f : B ⟶ B') (h : D ⟶ D') (hi : i ≫ f = i')
    (hr : r ≫ h = f ≫ r') (hs : s ≫ h = s')
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence f) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence h := by
  have : Mono (Under.mk i).hom := by change Mono i; infer_instance
  have : Mono (Under.mk i').hom := by change Mono i'; infer_instance
  let u : Under.mk i ⟶ Under.mk i' := Under.homMk f hi
  let m := ((Under.pushout g).map u).right
  have hm : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence m := isPrecompositionEquivalence_underPushout_map g u hf
  have hm₁ : pushout.inl i g ≫ m = f ≫ pushout.inl i' g := pushout.inl_desc _ _ _
  have hm₂ : pushout.inr i g ≫ m = pushout.inr i' g := pushout.inr_desc _ _ _
  have he : hP.isoPushout.hom ≫ m ≫ hP'.isoPushout.inv = h := by
    apply hP.hom_ext
    · rw [← Category.assoc, ← Category.assoc, hP.inl_isoPushout_hom,
        Category.assoc, ← Category.assoc, hm₁, Category.assoc,
        hP'.inl_isoPushout_inv, hr]
    · rw [← Category.assoc, ← Category.assoc, hP.inr_isoPushout_hom,
        Category.assoc, ← Category.assoc, hm₂, hP'.inr_isoPushout_inv, hs]
  rw [← he]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso hP.isoPushout).comp
    (hm.comp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso hP'.isoPushout.symm))

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
