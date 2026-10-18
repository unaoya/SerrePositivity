module

public import SerrePositivity.InfinityCategories.HomotopyLimits.SectionsFiberwiseComparison
public import SerrePositivity.InfinityCategories.Core.ConeAnodyne

/-!
概要：右ファイブレーションによる点上の slice の後合成は自明 Kan fibration。
方針：境界と右の一点の join を最後のホーンに同定し、slice の普遍性で充填を移す。
規約：元の全空間と底の quasicategory 性は要求しない。
使われ方：Kerodon 4.3.7.8 の双対、7.4.1.6、7.5.4.6 の錐の写像空間の比較 span。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet MorphismProperty
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 概要：境界と右の一点の join は標準単体の最後のホーンの逆像。
方針：連結写像の欠落頂点の表示で、右の唯一の頂点を除いた欠落を左因子に移す。
規約：n=0 も含む。
使われ方：Kerodon 4.3.7.8 の双対の right anodyne 性の生成セル。 -/
lemma rightConeBoundary_horn_preimage (n : ℕ) :
    (horn (n + 0 + 1) (Fin.last (n + 1))).preimage (joinStdSimplexIso.{u} n 0).hom =
      joinSubcomplexLeft (boundary n) (Δ[0] : SSet.{u}) := by
  ext ⟨⟨d⟩⟩ s
  change ((joinStdSimplexIso n 0).hom.app (Opposite.op ⦋d⦌) s ∈
    (horn (n + 0 + 1)
      (Fin.cast (by omega) (Fin.last (n + 1) : Fin ((n + 1) + (0 + 1))))).obj _) ↔ _
  rw [Join.mem_horn_joinStdSimplexIso_iff n 0 d s (Fin.last (n + 1)),
    Join.mem_joinSubcomplexLeft,
    Join.augMem_boundary_iff, Join.stdEncode, Join.missing_concat_iff]
  constructor
  · rintro (⟨v, _, hm⟩ | ⟨v, hv, _⟩)
    · exact ⟨v, hm⟩
    · have he : v.natAdd (n + 1) = Fin.last (n + 1) := by
        have : v = 0 := Fin.ext (by have := v.isLt; omega)
        rw [this]
        rfl
      exact (hv he).elim
  · rintro ⟨v, hm⟩
    refine Or.inl ⟨v, ?_, hm⟩
    intro he
    have hv := congrArg Fin.val he
    change v.val = n + 1 at hv
    have := v.isLt
    omega

/-- 概要：境界と右の一点の join の包含は right anodyne。
方針：標準単体の同型で最後のホーン包含へ移す。
規約：最後のホーンは right horn に含まれる。
使われ方：Kerodon 4.3.7.8 の双対の slice の後合成の境界充填。 -/
lemma joinBoundary_point_rightAnodyne (n : ℕ) :
    rightAnodyneExtensions (joinMap (boundary n).ι (𝟙 (Δ[0] : SSet.{u}))) := by
  have hh : rightAnodyneExtensions (horn.{u} (n + 0 + 1) (Fin.last (n + 1))).ι :=
    rightAnodyneExtensions_horn (Fin.last (n + 1)) (by change 0 < n + 1; omega)
  have hr : rightAnodyneExtensions
      (joinSubcomplexLeft (boundary n) (Δ[0] : SSet.{u})).ι := by
    rw [← rightConeBoundary_horn_preimage]
    exact (rightAnodyneExtensions.arrow_mk_iso_iff
      (Arrow.isoMk (subcomplexPreimageIso (horn (n + 0 + 1) (Fin.last (n + 1)))
        (joinStdSimplexIso n 0)) (joinStdSimplexIso n 0) (by rfl))).mpr hh
  have he := rightAnodyneExtensions.comp_mem
    (joinSubcomplexLeftIso (boundary n) (Δ[0] : SSet.{u})).hom
    (joinSubcomplexLeft (boundary n) (Δ[0] : SSet.{u})).ι
    (MorphismProperty.of_isIso _ _) hr
  simpa only [joinSubcomplexLeftIso_hom_ι] using he

/-- 概要：右ファイブレーションの点上の slice の後合成は全境界を持ち上げる。
方針：slice の curry の四角形を境界と右の一点の join の四角形へ移す。
規約：固定図式の始域は標準零単体。
使われ方：Kerodon 4.3.7.8 の双対、7.4.1.6 の写像空間の比較 span。 -/
lemma sliceOverPostcomp_boundary_lifting_of_rightFibration {E B : SSet.{u}}
    (c : (Δ[0] : SSet.{u}) ⟶ E) (r : E ⟶ B) [RightFibration r] (n : ℕ) :
    HasLiftingProperty (boundary n).ι (sliceOverPostcomp c r) := by
  constructor
  intro a b sq
  have hT : CommSq (sliceOverUncurry a)
      (joinMap (boundary n).ι (𝟙 (Δ[0] : SSet.{u}))) r (sliceOverUncurry b) := by
    constructor
    have he := congrArg sliceOverUncurry sq.w
    rw [sliceOverUncurry_postcomp, sliceOverUncurry_precomp] at he
    exact he
  have := joinBoundary_point_rightAnodyne n r RightFibration.mem
  let L := hT.lift
  have hfixed : joinInr (Δ[n] : SSet.{u}) Δ[0] ≫ L = c := by
    have he := congrArg
      (fun z ↦ joinInr (boundary n : SSet.{u}) (Δ[0] : SSet.{u}) ≫ z) hT.fac_left
    rw [← Category.assoc, joinInr_joinMap, Category.id_comp] at he
    exact he.trans (sliceOverUncurry_fixed a)
  refine CommSq.HasLift.mk' { l := sliceOverCurry L hfixed, fac_left := ?_, fac_right := ?_ }
  · apply sliceOverUncurry_injective c
    rw [sliceOverUncurry_precomp, sliceOverUncurry_curry]
    exact hT.fac_left
  · apply sliceOverUncurry_injective (c ≫ r)
    rw [sliceOverUncurry_postcomp, sliceOverUncurry_curry]
    exact hT.fac_right

/-- 概要：右ファイブレーションの点上の slice の後合成は自明 Kan fibration。
方針：全境界の持ち上げ性で判定する。
規約：E と B の quasicategory 性は不要。
使われ方：Kerodon 4.3.7.8 の双対、7.5.4.6 の比較射の始域への自明な射影。 -/
lemma sliceOverPostcomp_trivialKanFibration_of_rightFibration {E B : SSet.{u}}
    (c : (Δ[0] : SSet.{u}) ⟶ E) (r : E ⟶ B) [RightFibration r] :
    TrivialKanFibration (sliceOverPostcomp c r) :=
  (trivialKanFibration_iff_boundary _).2
    (sliceOverPostcomp_boundary_lifting_of_rightFibration c r)

end SerrePositivity.InfinityCategories.HomotopyLimits
