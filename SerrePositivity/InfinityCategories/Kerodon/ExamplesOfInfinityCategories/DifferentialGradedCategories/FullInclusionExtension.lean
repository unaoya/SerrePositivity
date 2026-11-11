module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.FullInclusionLift
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinVertexSurjectivity

/-! # 頂点を覆う写像に沿う充満部分圏への充填の持ち上げ

概要：境界側が全頂点を覆い部分圏内にあるなら、周囲の dg nerve の延長も部分圏へ持ち上がる。
方針：頂点上全射性で延長の全対象に P を戻し、range_inclusion による持ち上げと単射性を使う。
規約：HA Construction 1.3.1.6。使われ方：slice の極限性を充満 dg 部分圏へ反映する。

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

/-- 概要：全頂点を覆う写像に沿う周囲の延長は、元の部分圏の写像を延長する形で持ち上がる。
方針：境界の頂点から延長の全対象の P を得て像へ持ち上げ、包含の単射性で境界の一致を示す。
規約：HA Proposition 1.3.1.10。使われ方：正次元 slice 境界の充填を部分圏へ制限する。 -/
lemma fullInclusion_extension {T Z : SSet.{max u v}} (j : T ⟶ Z)
    (hj : Function.Surjective (j.app (op ⦋0⦌)))
    (a : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (DGFullSubcategory D P)) (F : Z ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
    (h : j ≫ F = a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion A D P)) :
    ∃ L : Z ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (DGFullSubcategory D P), j ≫ L = a ∧
      L ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion A D P) = F := by
  have hvertices : ∀ z : Z _⦋0⦌, P ((F.app _ z).obj 0) := by
    intro z
    obtain ⟨t, rfl⟩ := hj z
    have H := congrArg (fun q => (q.app (op ⦋0⦌) t).obj 0) h
    change (F.app _ (j.app _ t)).obj 0 = ((a.app _ t).obj 0).val at H
    rw [H]
    exact ((a.app _ t).obj 0).property
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fullInclusionLift A D P F hvertices, ?_, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fullInclusionLift_comp A D P F hvertices⟩
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion A D P))).1
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fullInclusionLift_comp]
  exact h

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
