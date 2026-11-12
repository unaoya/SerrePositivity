module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.FullSubcategory
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.DataComponents

/-! # 充満 dg 部分圏の nerve の包含の単射性

概要：充満 dg 部分圏の包含は dg nerve の各単体で単射である。
方針：対象の部分型の外延性と元と同じ Hom 成分を使う。
規約：HA Construction 1.3.1.6。使われ方：充満部分圏へ持ち上げた充填の一意性と境界一致。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open CategoryTheory Opposite DifferentialGraded
open scoped _root_.Simplicial

variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (P : D → Prop)

/-- 概要：充満 dg 部分圏の包含による単体の写像は単射。
方針：対象は部分型の外延性、Hom 成分は包含上の恒等写像の評価で比較する。
規約：HA Construction 1.3.1.6。使われ方：包含の単射性の各次数での検証。 -/
lemma map_inclusion_injective (n : ℕ) :
    Function.Injective (fun s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (DGFullSubcategory D P) n =>
      s.map (dgFullSubcategoryInclusion A D P)) := by
  intro s t hst
  have hobj : s.obj = t.obj := by
    funext i
    apply Subtype.ext
    exact congrArg (fun q : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D n => q.obj i) hst
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.ext hobj
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HomFamily.heq_of_pointwise hobj
  intro I a b k hI ha hb hk
  have H := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.hom_heq_of_eq (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.toSimplexData hst) I a b k hI ha hb hk
  exact H

/-- 概要：充満 dg 部分圏の包含の dg nerve の写像は単射射。
方針：自然変換の各成分の単射性から Mono を得る。
規約：HA Construction 1.3.1.6。使われ方：像の部分複体との同型と充填の反映。 -/
instance fullInclusion_mono : Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion A D P)) := by
  rw [NatTrans.mono_iff_mono_app]
  rintro ⟨⟨n⟩⟩
  rw [mono_iff_injective]
  exact map_inclusion_injective A D P n

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
