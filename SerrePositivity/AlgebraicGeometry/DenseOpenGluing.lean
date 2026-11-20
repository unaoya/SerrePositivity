module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.LocalLiftGluing
public import Mathlib.AlgebraicGeometry.Gluing

/-!
概要：KST §5、Stacks 080Y のスキーム論的に稠密な中心外開集合による支配射の大域貼り合わせ。
方針：局所射の基底交換式を使い、零核の開包含を重なりへ引き戻して一致を検出する。
規約：位相的な稠密性ではなく、中心外開包含の核が零であることを使う。
使われ方：アフィン局所的な admissible blowup 支配の大域化。
-/

@[expose] public noncomputable section

universe u v
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
variable {S Y T : Scheme.{u}} (s : Y ⟶ S) [IsSeparated s]
  (U : S.Opens) [IsIso (s ∣_ U)] (t : T ⟶ S)
  [QuasiCompact (t ⁻¹ᵁ U).ι] (hker : (t ⁻¹ᵁ U).ι.ker = ⊥)
  (𝒱 : T.OpenCover.{v}) (f : ∀ i, 𝒱.X i ⟶ Y)
  (hf : ∀ i, f i ≫ s = 𝒱.f i ≫ t)

include s U t hker hf

set_option backward.isDefEq.respectTransparency false in
/--
概要：零核の中心外開集合を持つ始域上で、基底上の局所射は重なりで一致する。
方針：中心外開包含を各被覆の成分へ引き戻し、局所的一意性を適用する。
規約：KST §5、Stacks 080Y、標的は U 上で同型かつ基底上で分離。
使われ方：局所的な支配射の貼り合わせ条件。
-/
theorem denseOpen_localMaps_compatible (i j : 𝒱.I₀) :
    pullback.fst (𝒱.f i) (𝒱.f j) ≫ f i = pullback.snd (𝒱.f i) (𝒱.f j) ≫ f j := by
  let q := pullback.snd (t ⁻¹ᵁ U).ι (𝒱.f i)
  refine local_lift_overlap_hom_ext s U (𝒱.f i) (𝒱.f j) (f i) (f j) ?_ q
    (pullback_snd_ker_eq_bot_of_openImmersion _ hker (𝒱.f i)) ?_
  · simp only [Category.assoc, hf]
    exact pullback.condition_assoc _
  · dsimp only [q]
    rw [hf i, ← pullback.condition_assoc]
    rintro _ ⟨x, rfl⟩
    exact (pullback.fst (t ⁻¹ᵁ U).ι (𝒱.f i) x).2

/--
概要：零核の中心外開集合によって基底上の局所射を貼り合わせた実際の大域射。
方針：中心外での同型と分離性から得た重なり上の一致を開被覆の貼り合わせに渡す。
規約：KST §5、Stacks 080Y、基底上の交換式を満たす任意の局所射族。
使われ方：アフィン支配射の大域化。
-/
def denseOpenGlue : T ⟶ Y :=
  𝒱.glueMorphisms f (denseOpen_localMaps_compatible s U t hker 𝒱 f hf)

set_option backward.isDefEq.respectTransparency false in
/--
概要：稠密な中心外開集合で貼り合わせた射は指定された基底射を持つ。
方針：始域の開被覆で局所交換式を確認する。
規約：KST §5、Stacks 080Y、基底 S への射の等式。
使われ方：大域の支配射の可換三角形。
-/
@[reassoc] theorem denseOpenGlue_base : denseOpenGlue s U t hker 𝒱 f hf ≫ s = t := by
  apply 𝒱.hom_ext
  intro i
  rw [denseOpenGlue, Scheme.Cover.ι_glueMorphisms_assoc, hf i]

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
