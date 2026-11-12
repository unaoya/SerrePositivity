module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Lax.LaxInclusions

public import SerrePositivity.KST.LocalizingInvariants.LaxStableCategory
public import SerrePositivity.KST.LocalizingInvariants.ZeroArrowFamily
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.LaxPullbackLift

/-!
概要：元の lax pullback に、両因子からの実際の全単体上の包含関手を構成する。
方針：零値関手を端に持つ矢印の全族を、指定端点を保つ F2 の lift へ渡す。
規約：完全性・随伴・充満忠実性は別の工程。使われ方：Tamme Prop. 10 の両包含。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.LaxInclusion

variable {C D E : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap D E)

/-- d ↦ (0,d,0→q d) は全単体上で定義された実 ∞ 関手。 -/
def fromD : D.obj ⟶ (laxCategory p q).obj :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxPullbackLift p.hom q.hom _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Lax.zeroC (𝟙 D.obj)
    (ZeroArrowFamily.ofHomotopy (ZeroArrowFamily.fromZero _ q.hom (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Lax.zeroC_post p)))
    (ZeroArrowFamily.ofHomotopy_source _) (by
      simpa only [Category.id_comp] using ZeroArrowFamily.ofHomotopy_target
        (ZeroArrowFamily.fromZero _ q.hom (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Lax.zeroC_post p)))

/-- c ↦ (c,0,p c→0) は全単体上で定義された実 ∞ 関手。 -/
def fromC : C.obj ⟶ (laxCategory p q).obj :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxPullbackLift p.hom q.hom (𝟙 C.obj) _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Lax.zeroD
    (ZeroArrowFamily.ofHomotopy (ZeroArrowFamily.toZero p.hom _ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Lax.zeroD_post q)))
    (by
      simpa only [Category.id_comp] using ZeroArrowFamily.ofHomotopy_source
        (ZeroArrowFamily.toZero p.hom _ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Lax.zeroD_post q)))
    (ZeroArrowFamily.ofHomotopy_target _)

lemma fromD_fst : fromD p q ≫ (laxFst p q).hom = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Lax.zeroC := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxPullbackLift_fst ..
lemma fromD_snd : fromD p q ≫ (laxSnd p q).hom = 𝟙 D.obj := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxPullbackLift_snd ..
lemma fromC_fst : fromC p q ≫ (laxFst p q).hom = 𝟙 C.obj := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxPullbackLift_fst ..
lemma fromC_snd : fromC p q ≫ (laxSnd p q).hom = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Lax.zeroD := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxPullbackLift_snd ..

end SerrePositivity.KST.LocalizingInvariants.LaxInclusion
