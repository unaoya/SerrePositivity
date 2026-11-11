module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.BinaryColimitHomExt
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.BinaryCoproductCocone
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.BinaryProducts

/-! # 安定 ∞ 圏のホモトピー圏の二項余積

概要：離散二点図式の余極限を h C の二項余積として公開する。
方針：降下射の存在と一意性から Mathlib の余極限を作る。
規約：加法構造を仮定しない。使われ方：安定ホモトピー圏の前加法構造。

対応節は Kerodon 7.6（Tag 03E8）。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits

/-- 概要：二点図式の普遍余錐の脚はホモトピー圏の普遍二項余錐となる。
方針：対象を頂点で表して降下射を選び、両脚による一意性を使う。
規約：値域は quasicategory。使われ方：二項余積の存在。 -/
def binaryColimit_isColimit {X : SSet.{u}} [Quasicategory X]
    {p : (Δ[0] : SSet.{u}) ⨿ Δ[0] ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c) :
    IsColimit (BinaryCofan.mk
      (SSet.Truncated.HomotopyCategory.homMk (c.leg _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryPointLeft))
      (SSet.Truncated.HomotopyCategory.homMk (c.leg _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryPointRight))) := by
  have hex (z : hoFunctor.obj X)
      (a : (SSet.HomotopyCategory.mk (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryPointLeft ≫ p)) :
        hoFunctor.obj X) ⟶ z)
      (b : (SSet.HomotopyCategory.mk (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryPointRight ≫ p)) :
        hoFunctor.obj X) ⟶ z) :
      ∃ f : (SSet.HomotopyCategory.mk c.vertex : hoFunctor.obj X) ⟶ z,
        SSet.Truncated.HomotopyCategory.homMk (c.leg _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryPointLeft) ≫ f = a ∧
        SSet.Truncated.HomotopyCategory.homMk (c.leg _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryPointRight) ≫ f = b := by
    obtain ⟨z, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective z
    exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.exists_binaryColimit_desc c hc z a b
  have huniq (z : hoFunctor.obj X)
      (f g : (SSet.HomotopyCategory.mk c.vertex : hoFunctor.obj X) ⟶ z)
      (hL : SSet.Truncated.HomotopyCategory.homMk (c.leg _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryPointLeft) ≫ f =
        SSet.Truncated.HomotopyCategory.homMk (c.leg _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryPointLeft) ≫ g)
      (hR : SSet.Truncated.HomotopyCategory.homMk (c.leg _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryPointRight) ≫ f =
        SSet.Truncated.HomotopyCategory.homMk (c.leg _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryPointRight) ≫ g) : f = g := by
    obtain ⟨z, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective z
    exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryColimit_hom_ext c hc z f g hL hR
  apply BinaryCofan.isColimitMk (fun s => (hex s.pt s.inl s.inr).choose)
    (fun s => (hex s.pt s.inl s.inr).choose_spec.1)
    (fun s => (hex s.pt s.inl s.inr).choose_spec.2)
  intro s m hL hR
  exact huniq s.pt m (hex s.pt s.inl s.inr).choose
    (hL.trans (hex s.pt s.inl s.inr).choose_spec.1.symm)
    (hR.trans (hex s.pt s.inl s.inr).choose_spec.2.symm)

/-- 概要：二点図式の余極限があれば、その二つの値は h C で余積を持つ。
方針：普遍余錐の脚から colimit cocone を与える。
規約：安定性は不要。使われ方：指定二頂点の余積の転送。 -/
lemma hasBinaryCoproduct_of_binaryColimit {X : SSet.{u}} [Quasicategory X]
    {p : (Δ[0] : SSet.{u}) ⨿ Δ[0] ⟶ X} (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit p) :
    CategoryTheory.Limits.HasColimit (pair
      (SSet.HomotopyCategory.mk (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryPointLeft ≫ p)) : hoFunctor.obj X)
      (SSet.HomotopyCategory.mk (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryPointRight ≫ p)))) := by
  obtain ⟨c, hc⟩ := hp
  exact ⟨⟨_, binaryColimit_isColimit c hc⟩⟩

/-- 概要：安定 ∞ 圏のホモトピー圏は二項余積を持つ。
方針：二対象を頂点で表し、安定性から離散二点図式の余極限を得る。
規約：前加法構造はまだ使わない。使われ方：h C の加法構造の構成。 -/
instance hasBinaryCoproducts_ho {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] :
    HasBinaryCoproducts (hoFunctor.obj X) := by
  have hpair (a b : hoFunctor.obj X) : CategoryTheory.Limits.HasColimit (pair a b) := by
    obtain ⟨x, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective a
    obtain ⟨y, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective b
    have h := hasBinaryCoproduct_of_binaryColimit (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.hasColimit_binaryPointDiagram x y)
    change CategoryTheory.Limits.HasColimit (pair
      (SSet.HomotopyCategory.mk x : X.HomotopyCategory) (SSet.HomotopyCategory.mk y))
    simpa only [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryPointDiagram, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryPointLeft, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryPointRight,
      coprod.inl_desc, coprod.inr_desc, Equiv.apply_symm_apply] using h
  let {a b : hoFunctor.obj X} : CategoryTheory.Limits.HasColimit (pair a b) := hpair a b
  exact hasBinaryCoproducts_of_hasColimit_pair (hoFunctor.obj X)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits
