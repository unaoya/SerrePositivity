module

public import SerrePositivity.InfinityCategories.Core.SliceRestriction

/-!
概要：点を左から join する関手は単射を left anodyne 射に写す。
方針：境界セルが最初のホーンに対応することを示し、coslice の普遍性と境界セル分解で広げる。
規約：通常の圏の始対象からの錐の retract に適用する。
使われ方：Kerodon Lemma 4.3.7.8、Corollary 4.7.3.22 の双対、HTT §4.1.1。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Limits SSet MorphismProperty
open scoped Simplicial

namespace SerrePositivity.InfinityCategories

/-- 概要：点と境界の join は、標準単体の最初のホーンの逆像。
方針：連結写像で零番目以外の欠落頂点は右因子の欠落頂点に等しい。
規約：n=0 の場合も含む。
使われ方：Kerodon Lemma 4.3.7.8 の left anodyne 性の生成セル。 -/
lemma coneBoundary_horn_preimage (n : ℕ) :
    (horn (0 + n + 1) 0).preimage (joinStdSimplexIso.{u} 0 n).hom =
      joinSubcomplexRight Δ[0] (boundary n) := by
  ext ⟨⟨d⟩⟩ s
  change ((joinStdSimplexIso 0 n).hom.app (Opposite.op ⦋d⦌) s ∈
    (horn (0 + n + 1) (Fin.cast (by omega) (0 : Fin (1 + (n + 1))))).obj _) ↔ _
  rw [Join.mem_horn_joinStdSimplexIso_iff, Join.mem_joinSubcomplexRight,
    Join.augMem_boundary_iff, Join.stdEncode, Join.missing_concat_iff]
  constructor
  · rintro (⟨v, hv, _⟩ | ⟨v, _, hm⟩)
    · have he : v.castAdd (n + 1) = (0 : Fin (1 + (n + 1))) := by
        have : v = 0 := Fin.ext (by have := v.isLt; omega)
        rw [this]; rfl
      exact (hv he).elim
    · exact ⟨v, hm⟩
  · rintro ⟨v, hm⟩
    refine Or.inr ⟨v, ?_, hm⟩
    intro he
    have hv := congrArg Fin.val he
    change 1 + v.val = 0 at hv
    omega

/-- 概要：点と境界の join から点と標準単体の join への包含は left anodyne。
方針：標準単体の同型で最初のホーン包含に移す。
規約：最初のホーンは left horn、最後のホーンではない。
使われ方：Kerodon Lemma 4.3.7.8 の生成セル。 -/
lemma joinPoint_boundary_leftAnodyne (n : ℕ) :
    leftAnodyneExtensions (joinMap (𝟙 (Δ[0] : SSet.{u})) (boundary n).ι) := by
  have hh : leftAnodyneExtensions (horn.{u} (0 + n + 1) 0).ι := by
    rw [Nat.zero_add]
    exact leftAnodyneExtensions_horn 0 (by change 0 < n + 1; omega)
  have hr : leftAnodyneExtensions (joinSubcomplexRight (Δ[0] : SSet.{u}) (boundary n)).ι := by
    rw [← coneBoundary_horn_preimage]
    exact (leftAnodyneExtensions.arrow_mk_iso_iff
      (Arrow.isoMk (subcomplexPreimageIso (horn (0 + n + 1) 0) (joinStdSimplexIso 0 n))
        (joinStdSimplexIso 0 n) (by rfl))).2 hh
  have he := leftAnodyneExtensions.comp_mem
    (joinSubcomplexRightIso (Δ[0] : SSet.{u}) (boundary n)).hom
    (joinSubcomplexRight (Δ[0] : SSet.{u}) (boundary n)).ι
    (MorphismProperty.of_isIso _ _) hr
  simpa only [joinSubcomplexRightIso_hom_ι] using he

/-- 概要：左ファイブレーションによる点下の coslice の射は、境界包含に対して持ち上げ性を持つ。
方針：curry の正方形を点と境界の join の正方形に直し、最初のホーンの持ち上げを使う。
規約：固定図式 p の始域は Δ[0]。
使われ方：Kerodon Lemma 4.3.7.8 の単射への閉包。 -/
lemma sliceUnderPostcomp_boundary_lifting {X Y : SSet.{u}} (p : (Δ[0] : SSet.{u}) ⟶ X)
    (q : X ⟶ Y) [LeftFibration q] (n : ℕ) :
    HasLiftingProperty (boundary n).ι (sliceUnderPostcomp p q) := by
  constructor
  intro a b sq
  let G := sliceUnderUncurry a
  let H := sliceUnderUncurry b
  have hT : CommSq G (joinMap (𝟙 (Δ[0] : SSet.{u})) (boundary n).ι) q H := by
    constructor
    have he := congrArg sliceUnderUncurry sq.w
    rw [sliceUnderUncurry_postcomp, sliceUnderUncurry_precomp] at he
    exact he
  have := joinPoint_boundary_leftAnodyne n q LeftFibration.mem
  let L := hT.lift
  have hfixed : joinInl (Δ[0] : SSet.{u}) Δ[n] ≫ L = p := by
    have he := congrArg (fun z ↦ joinInl (Δ[0] : SSet.{u}) (boundary n : SSet.{u}) ≫ z) hT.fac_left
    rw [← Category.assoc, joinInl_joinMap, Category.id_comp] at he
    exact he.trans (sliceUnderUncurry_fixed a)
  refine CommSq.HasLift.mk' { l := sliceUnderCurry L hfixed, fac_left := ?_, fac_right := ?_ }
  · apply sliceUnderUncurry_injective p
    rw [sliceUnderUncurry_precomp, sliceUnderUncurry_curry]
    exact hT.fac_left
  · apply sliceUnderUncurry_injective (p ≫ q)
    rw [sliceUnderUncurry_postcomp, sliceUnderUncurry_curry]
    exact hT.fac_right

/-- 概要：左ファイブレーションによる点下の coslice の射は trivial Kan fibration。
方針：全境界の持ち上げ性と単射の境界セル分解を使う。
規約：X と Y の quasicategory 性は要求しない。
使われ方：Kerodon Lemma 4.3.7.8 の全単射に対する持ち上げ。 -/
lemma sliceUnderPostcomp_trivialKanFibration {X Y : SSet.{u}}
    (p : (Δ[0] : SSet.{u}) ⟶ X) (q : X ⟶ Y) [LeftFibration q] :
    TrivialKanFibration (sliceUnderPostcomp p q) := by
  rw [trivialKanFibration_iff_boundary]
  exact sliceUnderPostcomp_boundary_lifting p q

/-- 概要：点を左から join すると任意の単射は left anodyne になる。
方針：点下の coslice の射の全単射に対する持ち上げ性を、普遍性で join の射へ戻す。
規約：f に anodyne 性を仮定しない。
使われ方：Kerodon Lemma 4.3.7.8、Corollary 4.7.3.22 の始対象の頂点包含。 -/
lemma joinPoint_mono_leftAnodyne {A B : SSet.{u}} (f : A ⟶ B) [Mono f] :
    leftAnodyneExtensions (joinMap (𝟙 (Δ[0] : SSet.{u})) f) := by
  intro X Y q hq
  have : LeftFibration q := ⟨hq⟩
  constructor
  intro a b sq
  let p := joinInl (Δ[0] : SSet.{u}) A ≫ a
  have hb : joinInl (Δ[0] : SSet.{u}) B ≫ b = p ≫ q := by
    have he := congrArg (fun z ↦ joinInl (Δ[0] : SSet.{u}) A ≫ z) sq.w
    rw [← Category.assoc (joinInl (Δ[0] : SSet.{u}) A)
      (joinMap (𝟙 Δ[0]) f) b, joinInl_joinMap, Category.id_comp] at he
    exact he.symm
  have hs : CommSq (sliceUnderCurry a rfl) f (sliceUnderPostcomp p q) (sliceUnderCurry b hb) := by
    constructor
    apply sliceUnderUncurry_injective (p ≫ q)
    rw [sliceUnderUncurry_postcomp, sliceUnderUncurry_precomp,
      sliceUnderUncurry_curry, sliceUnderUncurry_curry]
    exact sq.w
  have := (sliceUnderPostcomp_trivialKanFibration p q).mem f inferInstance
  refine CommSq.HasLift.mk' { l := sliceUnderUncurry hs.lift, fac_left := ?_, fac_right := ?_ }
  · have he := congrArg sliceUnderUncurry hs.fac_left
    rw [sliceUnderUncurry_precomp, sliceUnderUncurry_curry] at he
    exact he
  · have he := congrArg sliceUnderUncurry hs.fac_right
    rw [sliceUnderUncurry_postcomp, sliceUnderUncurry_curry] at he
    exact he

end SerrePositivity.InfinityCategories
