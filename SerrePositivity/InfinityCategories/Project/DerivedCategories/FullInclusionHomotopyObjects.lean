module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FullInclusionHomotopyFaithful

/-! # 充満 dg 包含の h の対象写像の単射性

概要：充満 dg 部分圏の包含は通常の h の対象でも単射。
方針：道の商の対象は頂点であり、零単体と dg 対象の同値から部分型の等式に戻す。
規約：対象の閉性は不要。使われ方：D7 の Arrow 成分の包含による反映。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] (P : D → Prop)

/-- 充満 dg 包含が h に誘導する関手の対象写像は単射。 -/
lemma fullInclusionHo_obj_injective : Function.Injective
    (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion R D P))).toFunctor.obj := by
  intro x y h
  apply SSet.Truncated.HomotopyCategory.ext
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.injective
  apply Subtype.ext
  have hh := congrArg (fun z : hoFunctor.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D) => z.as.as) h
  exact congrArg (fun z : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R D 0 => z.obj 0) hh

end SerrePositivity.InfinityCategories.Project.DerivedCategories
