module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHomTransport
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
概要：任意の引き戻し四角形の pinched 写像空間への族の持ち上げ。
方針：pinched 族を join 上へ展開し、元の引き戻しの普遍性で持ち上げる。
規約：一致条件は元の空間への族の射の等式として指定する。
使われ方：相対標的の写像空間の引き戻し表示。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：一致する二つの pinched 族を任意の引き戻しの pinched 族へ持ち上げる。
方針：join 上で持ち上げ、両端の固定条件を二つの射影で確認する。
規約：quasicategory 性は不要。
使われ方：写像空間の引き戻しの普遍性の存在部分。 -/
def pinchedHomPullbackLift {A P X Y B : SSet.{u}}
    {a : P ⟶ X} {b : P ⟶ Y} {p : X ⟶ B} {q : Y ⟶ B}
    (h : IsPullback a b p q) (v w : P _⦋0⦌)
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (a.app (Opposite.op ⦋0⦌) v) (a.app (Opposite.op ⦋0⦌) w))
    (g : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (b.app (Opposite.op ⦋0⦌) v) (b.app (Opposite.op ⦋0⦌) w))
    (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomUncurry f ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomUncurry g ≫ q) : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom v w := by
  let L := h.lift (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomUncurry f) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomUncurry g) hc
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomCurry L
  · apply h.hom_ext
    · rw [Category.assoc, h.lift_fst, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomUncurry_inl, SSet.const_comp]
    · rw [Category.assoc, h.lift_snd, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomUncurry_inl, SSet.const_comp]
  · apply h.hom_ext
    · rw [Category.assoc, h.lift_fst, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomUncurry_inr, SSet.yonedaEquiv_symm_comp]
    · rw [Category.assoc, h.lift_snd, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomUncurry_inr, SSet.yonedaEquiv_symm_comp]

/-- 概要：任意の引き戻しへの pinched 族の持ち上げは元の族を展開して得る。
方針：pinched curry と uncurry の往復を使う。
規約：境界の固定条件の証明は射に影響しない。
使われ方：両射影との可換性と一意性。 -/
lemma pinchedHomPullbackLift_uncurry {A P X Y B : SSet.{u}}
    {a : P ⟶ X} {b : P ⟶ Y} {p : X ⟶ B} {q : Y ⟶ B}
    (h : IsPullback a b p q) (v w : P _⦋0⦌) (f g hc) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomUncurry (pinchedHomPullbackLift (A := A) h v w f g hc) =
      h.lift (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomUncurry f) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomUncurry g) hc := by
  unfold pinchedHomPullbackLift
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomUncurry_curry]

/-- 概要：pinched 族の持ち上げの第一射影は元の第一の族。
方針：展開した族で引き戻しの第一射影を計算する。
規約：全パラメータで成立する。
使われ方：写像空間の引き戻しの第一射影。 -/
lemma pinchedHomPullbackLift_fst {A P X Y B : SSet.{u}}
    {a : P ⟶ X} {b : P ⟶ Y} {p : X ⟶ B} {q : Y ⟶ B}
    (h : IsPullback a b p q) (v w : P _⦋0⦌) (f g hc) :
    pinchedHomPullbackLift (A := A) h v w f g hc ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap a v w = f := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomUncurry_injective
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomUncurry_postcomp, pinchedHomPullbackLift_uncurry, h.lift_fst]

/-- 概要：pinched 族の持ち上げの第二射影は元の第二の族。
方針：展開した族で引き戻しの第二射影を計算する。
規約：全パラメータで成立する。
使われ方：写像空間の引き戻しの第二射影。 -/
lemma pinchedHomPullbackLift_snd {A P X Y B : SSet.{u}}
    {a : P ⟶ X} {b : P ⟶ Y} {p : X ⟶ B} {q : Y ⟶ B}
    (h : IsPullback a b p q) (v w : P _⦋0⦌) (f g hc) :
    pinchedHomPullbackLift (A := A) h v w f g hc ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap b v w = g := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomUncurry_injective
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomUncurry_postcomp, pinchedHomPullbackLift_uncurry, h.lift_snd]

/-- 概要：任意の引き戻しの pinched 族は両方の射影で決まる。
方針：族を展開し、元の引き戻しの一意性を適用する。
規約：パラメータの単体集合は任意。
使われ方：写像空間の引き戻しの普遍性の一意性部分。 -/
lemma pinchedHomPullback_hom_ext {A P X Y B : SSet.{u}}
    {a : P ⟶ X} {b : P ⟶ Y} {p : X ⟶ B} {q : Y ⟶ B}
    (h : IsPullback a b p q) (v w : P _⦋0⦌) {f g : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom v w}
    (hf : f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap a v w = g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap a v w)
    (hg : f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap b v w = g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap b v w) : f = g := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomUncurry_injective
  apply h.hom_ext
  · simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomUncurry_postcomp] using congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomUncurry hf
  · simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomUncurry_postcomp] using congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomUncurry hg

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
