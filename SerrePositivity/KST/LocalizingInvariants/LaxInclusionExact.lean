module

public import SerrePositivity.KST.LocalizingInvariants.LaxInclusions
public import SerrePositivity.KST.LocalizingInvariants.ZeroMaps

/-!
概要：元の lax pullback の両包含は完全関手である。
方針：零対象と cofiber 列を両射影で判定し、零関手と恒等関手へ還元する。
規約：完全性を包含の入力にしない。使われ方：K-8 の半直交分解。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.LaxInclusion

variable {C D E : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap D E)

lemma preservesZero_of_components {K : SSet.{u}} (F : K ⟶ (laxCategory p q).obj)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (F ≫ (laxFst p q).hom)] [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (F ≫ (laxSnd p q).hom)] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PreservesZeroVertices F := by
  intro x hx
  have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesZero (F := F ≫ (laxFst p q).hom) x hx
  have hd := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesZero (F := F ≫ (laxSnd p q).hom) x hx
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.isZeroVertex_laxPullback_of_components p.hom q.hom (F.app _ x) hc hd
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesZero (F := p.hom) _ hc)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesZero (F := q.hom) _ hd)

lemma exact_of_components {K : SSet.{u}} (F : K ⟶ (laxCategory p q).obj)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (F ≫ (laxFst p q).hom)] [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (F ≫ (laxSnd p q).hom)] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor F where
  preservesZero := preservesZero_of_components p q F
  preservesCofiber t ht := by
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.isPushoutSquare_laxPullback_iff_of_zero_corner p.hom q.hom
      (t.map F (preservesZero_of_components p q F))).2
    exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesCofiber (F := F ≫ (laxFst p q).hom) t ht,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesCofiber (F := F ≫ (laxSnd p q).hom) t ht⟩

instance fromD_isExact : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (fromD p q) := by
  have hz : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Lax.zeroC : D.obj ⟶ C.obj) := isExact_of_zero_values _ (by
    intro x
    rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Lax.zeroC, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroDiagram_const_vertex]
    exact (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.chosenZeroVertex C.obj).isZero)
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (fromD p q ≫ (laxFst p q).hom) := (fromD_fst p q).symm ▸ hz
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (fromD p q ≫ (laxSnd p q).hom) :=
    (fromD_snd p q).symm ▸ inferInstanceAs (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (𝟙 D.obj))
  exact exact_of_components p q _

instance fromC_isExact : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (fromC p q) := by
  have hz : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Lax.zeroD : C.obj ⟶ D.obj) := isExact_of_zero_values _ (by
    intro x
    rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Lax.zeroD, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroDiagram_const_vertex]
    exact (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.chosenZeroVertex D.obj).isZero)
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (fromC p q ≫ (laxFst p q).hom) :=
    (fromC_fst p q).symm ▸ inferInstanceAs (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (𝟙 C.obj))
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (fromC p q ≫ (laxSnd p q).hom) := (fromC_snd p q).symm ▸ hz
  exact exact_of_components p q _

/-- 元の D 包含を完全関手に束ねる。 -/
def exactFromD : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap D (laxCategory p q) := ⟨fromD p q, inferInstance⟩

/-- 元の C 包含を完全関手に束ねる。 -/
def exactFromC : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C (laxCategory p q) := ⟨fromC p q, inferInstance⟩

end SerrePositivity.KST.LocalizingInvariants.LaxInclusion
