module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.HomotopyBinaryBiproduct
public import Mathlib.CategoryTheory.Preadditive.OfBiproducts

/-! # ホモトピー圏の射の加法逆元

概要：双積から得た Hom の可換モノイドの全ての射は加法逆元を持つ。
方針：第一射影に第二射影との合成を加えた左逆の積性に、零と恒等射を持ち上げる。
規約：可換モノイド構造は局所 instance として扱う。使われ方：h C の前加法構造。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：安定な quasicategory の Hom は双積による可換モノイド構造を持つ。
方針：Mathlib の二項双積からの Eckmann–Hilton 構成を使う。
規約：大域 instance は前加法構造にまとめる。使われ方：加法逆元の存在証明。 -/
@[instance_reducible]
def stableHomAddCommMonoid {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    (A B : hoFunctor.obj X) : AddCommMonoid (A ⟶ B) :=
  SemiadditiveOfBinaryBiproducts.addCommMonoidHomOfHasBinaryBiproducts A B

attribute [local instance] stableHomAddCommMonoid

/-- 概要：零始点の押し出しの二入力間の任意の射には加法左逆元がある。
方針：第一射影に第二射影との合成を加えた左逆で積を作り、零と恒等射を持ち上げる。
規約：双積の可換モノイドの加法を使う。使われ方：任意の Hom への逆元の転送。 -/
lemma exists_additiveInverse_of_zeroSourcePushout {X : SSet.{u}} [Quasicategory X]
    [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] (R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) (hR : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare R)
    (hz : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex R 0 0))
    (f : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoVertex R 0 1 ⟶ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoVertex R 1 0) :
    ∃ g : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoVertex R 0 1 ⟶ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoVertex R 1 0, g + f = 0 := by
  let p := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroSourceCoproductFst R hR hz.1
  let q := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroSourceCoproductSnd R hR hz.1
  let r := p + q ≫ f
  have hr : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoRight R ≫ r = 𝟙 _ := by
    rw [SemiadditiveOfBinaryBiproducts.comp_add, ← Category.assoc,
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroSourceCoproduct_right_fst, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroSourceCoproduct_right_snd, zero_comp, add_zero]
  let hp := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroSourcePushout_isBinaryProduct_of_retraction R hR hz r hr
  let j := BinaryFan.IsLimit.lift hp 0 (𝟙 (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoVertex R 0 1))
  have hjr : j ≫ r = 0 := BinaryFan.IsLimit.lift_fst hp _ _
  have hjq : j ≫ q = 𝟙 _ := BinaryFan.IsLimit.lift_snd hp _ _
  refine ⟨j ≫ p, ?_⟩
  have he : j ≫ r = (j ≫ p) + f := by
    rw [SemiadditiveOfBinaryBiproducts.comp_add, ← Category.assoc, hjq, Category.id_comp]
  exact he.symm.trans hjr

/-- 概要：安定な quasicategory の任意の Hom の全ての射に加法左逆元がある。
方針：二対象を頂点で表し、その二入力を持つ零始点の押し出しに前補題を適用する。
規約：選んだ双積からの可換モノイドの加法。使われ方：Hom の可換群構造。 -/
lemma exists_stableHom_additiveInverse {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    {A B : hoFunctor.obj X} (f : A ⟶ B) : ∃ g : A ⟶ B, g + f = 0 := by
  obtain ⟨x, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective A
  obtain ⟨y, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective B
  obtain ⟨R, hz, hy, hx, hR⟩ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.exists_zeroSourcePushoutSquare y x
  have hp : ∀ f : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoVertex R 0 1 ⟶ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoVertex R 1 0,
      ∃ g : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoVertex R 0 1 ⟶ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoVertex R 1 0, g + f = 0 :=
    exists_additiveInverse_of_zeroSourcePushout R hR hz
  have ha : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoVertex R 0 1 = (SSet.HomotopyCategory.mk x : hoFunctor.obj X) :=
    congrArg (fun z => (SSet.HomotopyCategory.mk z : hoFunctor.obj X)) hx
  have hb : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoVertex R 1 0 = (SSet.HomotopyCategory.mk y : hoFunctor.obj X) :=
    congrArg (fun z => (SSet.HomotopyCategory.mk z : hoFunctor.obj X)) hy
  rw [ha, hb] at hp
  exact hp f

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
