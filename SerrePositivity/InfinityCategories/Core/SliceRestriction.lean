module

public import SerrePositivity.InfinityCategories.Core.Terminal
public import SerrePositivity.InfinityCategories.Core.JoinFunctor

/-!
概要：left anodyne 射に沿う slice の制限は trivial Kan fibration。
方針：境界包含との pushout-join の内 anodyne 性を slice の普遍性で持ち上げ問題に移す。
規約：slice の制限は図式の変数に反変。
使われ方：Kerodon Corollary 4.3.6.14、HTT §4.1.1 の始対象による制限。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Limits SSet MorphismProperty
open scoped Simplicial

namespace SerrePositivity.InfinityCategories

/-- 概要：left anodyne な部分複体への制限は任意の部分複体包含に対して持ち上げ性を持つ。
方針：二つの錐を pushout-join 上で貼り合わせ、A2c と X の内部ホーン充填で延長する。
規約：試験する A₀⊆A に anodyne 性は要求しない。
使われ方：Kerodon Corollary 4.3.6.14、HTT §4.1.1 の制限の充填。 -/
lemma sliceOverRestrict_hasLiftingProperty {A K X : SSet.{u}} [Quasicategory X]
    (p : K ⟶ X) (A₀ : A.Subcomplex) (K₀ : K.Subcomplex)
    (hK : leftAnodyneExtensions K₀.ι) : HasLiftingProperty A₀.ι (sliceOverRestrict p K₀.ι) := by
  constructor
  intro a b sq
  let G := sliceOverUncurry a
  let H := sliceOverUncurry b
  have hover : joinMap (𝟙 (A₀ : SSet.{u})) K₀.ι ≫ G =
      joinMap A₀.ι (𝟙 (K₀ : SSet.{u})) ≫ H := by
    have hh := congrArg sliceOverUncurry sq.w
    rw [sliceOverUncurry_restrict, sliceOverUncurry_precomp] at hh
    exact hh
  let hs := joinUnion_isPushout A₀ K₀
  let T := hs.desc G H hover
  have hT : CommSq T (joinUnion A₀ K₀).ι (terminal.from X)
      (terminal.from (join A K)) := ⟨terminal.hom_ext _ _⟩
  have := joinUnion_innerAnodyne_of_leftAnodyne A₀ K₀ hK (terminal.from X) InnerFibration.mem
  let L := hT.lift
  have hleft : joinMap A₀.ι (𝟙 K) ≫ L = G := by
    rw [← joinUnionLeft_ι, Category.assoc]
    change joinUnionLeft A₀ K₀ ≫ ((joinUnion A₀ K₀).ι ≫ hT.lift) = G
    rw [hT.fac_left]
    exact hs.inl_desc G H hover
  have hright : joinMap (𝟙 A) K₀.ι ≫ L = H := by
    rw [← joinUnionRight_ι, Category.assoc]
    change joinUnionRight A₀ K₀ ≫ ((joinUnion A₀ K₀).ι ≫ hT.lift) = H
    rw [hT.fac_left]
    exact hs.inr_desc G H hover
  have hfixed : joinInr A K ≫ L = p := by
    have hh := congrArg (fun z ↦ joinInr (A₀ : SSet.{u}) K ≫ z) hleft
    rw [← Category.assoc, joinInr_joinMap, Category.id_comp] at hh
    exact hh.trans (sliceOverUncurry_fixed a)
  refine CommSq.HasLift.mk' { l := sliceOverCurry L hfixed, fac_left := ?_, fac_right := ?_ }
  · apply sliceOverUncurry_injective p
    rw [sliceOverUncurry_precomp, sliceOverUncurry_curry]
    exact hleft
  · apply sliceOverUncurry_injective (K₀.ι ≫ p)
    rw [sliceOverUncurry_restrict, sliceOverUncurry_curry]
    exact hright

/-- 概要：left anodyne な部分複体への slice の制限は trivial Kan fibration。
方針：任意の境界包含に対する持ち上げ性で判定する。
規約：X は quasicategory、図式 p と部分複体は任意。
使われ方：Kerodon Corollary 4.3.6.14、HTT §4.1.1 の始対象による制限。 -/
lemma sliceOverRestrict_subcomplex_trivialKanFibration {K X : SSet.{u}} [Quasicategory X]
    (p : K ⟶ X) (K₀ : K.Subcomplex) (hK : leftAnodyneExtensions K₀.ι) :
    TrivialKanFibration (sliceOverRestrict p K₀.ι) := by
  rw [trivialKanFibration_iff_boundary]
  intro n
  exact sliceOverRestrict_hasLiftingProperty p (boundary n) K₀ hK

/-- 概要：slice の制限は図式の合成に反変。
方針：右因子の joinMap の合成則を各錐に適用する。
規約：f の後に g を適用した図式への制限は g、f の順。
使われ方：Kerodon Corollary 4.3.6.14 の一般の単射への移送。 -/
lemma sliceOverRestrict_comp {K₀ K₁ K X : SSet.{u}} (p : K ⟶ X)
    (f : K₀ ⟶ K₁) (g : K₁ ⟶ K) :
    sliceOverRestrict p (f ≫ g) = sliceOverRestrict p g ≫ sliceOverRestrict (g ≫ p) f := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro σ
  apply Subtype.ext
  change joinMap (𝟙 _) (f ≫ g) ≫ σ.val =
    joinMap (𝟙 _) f ≫ (joinMap (𝟙 _) g ≫ σ.val)
  rw [← Category.assoc, ← joinMap_comp, Category.id_comp]

/-- 概要：同型による図式の制限は slice の同型。
方針：次数ごとの前合成の逆に joinMap の逆射を用いる。
規約：固定条件は元の同型の逆関係で保たれる。
使われ方：Kerodon Corollary 4.3.6.14 の単射の像への分解。 -/
lemma sliceOverRestrict_isIso {K₀ K X : SSet.{u}} (p : K ⟶ X) (f : K₀ ⟶ K) [IsIso f] :
    IsIso (sliceOverRestrict p f) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro n
  have : IsIso (joinMap (𝟙 (stdSimplex.obj n.unop)) f) :=
    (joinRightFunctor (stdSimplex.obj n.unop)).map_isIso f
  rw [isIso_iff_bijective]
  constructor
  · intro σ τ h
    apply Subtype.ext
    apply (cancel_epi (joinMap (𝟙 (stdSimplex.obj n.unop)) f)).1
    exact congrArg Subtype.val h
  · intro σ
    let τ : (sliceOver p).obj n :=
      ⟨joinMap (𝟙 (stdSimplex.obj n.unop)) (inv f) ≫ σ.val, by
        rw [← Category.assoc, joinInr_joinMap, Category.assoc, σ.property,
          IsIso.inv_hom_id_assoc]⟩
    refine ⟨τ, Subtype.ext ?_⟩
    change joinMap (𝟙 _) f ≫ (joinMap (𝟙 _) (inv f) ≫ σ.val) = σ.val
    rw [← Category.assoc, ← joinMap_comp, Category.id_comp, IsIso.hom_inv_id,
      joinMap_id, Category.id_comp]

/-- 概要：left anodyne な任意の単射による slice の制限は trivial Kan fibration。
方針：単射を像への同型と部分複体包含に分け、同型による制限の不変性を使う。
規約：部分複体の包含という特定の表示は仮定しない。
使われ方：Kerodon Corollary 4.3.6.14、HTT §4.1.1 の頂点包含への適用。 -/
lemma sliceOverRestrict_trivialKanFibration {K₀ K X : SSet.{u}} [Quasicategory X]
    (p : K ⟶ X) (f : K₀ ⟶ K) [Mono f] (hf : leftAnodyneExtensions f) :
    TrivialKanFibration (sliceOverRestrict p f) := by
  let R : K.Subcomplex := Subfunctor.range f
  have := Subfunctor.instIsIsoFunctorTypeToRangeOfMono f
  have hR : leftAnodyneExtensions R.ι :=
    (leftAnodyneExtensions.arrow_mk_iso_iff
      (Arrow.isoMk (asIso (Subfunctor.toRange f)) (Iso.refl K) (by rfl))).1 hf
  have hT := sliceOverRestrict_subcomplex_trivialKanFibration p R hR
  have := sliceOverRestrict_isIso (R.ι ≫ p) (Subfunctor.toRange f)
  have he : f = Subfunctor.toRange f ≫ R.ι := rfl
  rw [he, sliceOverRestrict_comp]
  constructor
  exact trivialKanFibrations.comp_mem _ _ hT.mem (MorphismProperty.rlp_of_isIso _ _)

end SerrePositivity.InfinityCategories
