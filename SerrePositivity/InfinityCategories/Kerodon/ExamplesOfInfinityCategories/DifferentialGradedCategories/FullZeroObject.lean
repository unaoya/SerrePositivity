module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.FullInclusionExtension
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ZeroObject

/-! # 充満 dg 部分圏の零対象

概要：充満 dg 部分圏の包含は始対象性・終対象性を反映し、零複体を含む部分圏は零対象を持つ。
方針：周囲で正次元境界を充填し、全頂点を覆う境界からその充填を持ち上げる。
規約：HTT §1.2.12、HA Construction 1.3.1.6。使われ方：導来 ∞ 圏の零対象。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open CategoryTheory Opposite DifferentialGraded
open scoped _root_.Simplicial ZeroObject

variable (A : Type u) [CommRing A]

/-- 概要：充満 dg 部分圏の包含は Terminal 頂点の充填条件を反映する。
方針：周囲の境界充填を、全頂点を覆う境界に沿って部分圏へ持ち上げる。
規約：HTT §1.2.12。使われ方：零対象の Terminal 性を部分圏へ戻す。 -/
lemma isTerminalVertex_of_fullInclusion (D : Type v) [DGCategory A D] (P : D → Prop)
    (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (DGFullSubcategory D P)) _⦋0⦌)
    (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion A D P)).app _ x)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex x := by
  intro n b hb
  let q := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion A D P)
  have hb' : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1)) ≫ (b ≫ q) =
      SSet.yonedaEquiv.symm (q.app _ x) := by
    rw [← Category.assoc, hb, SSet.yonedaEquiv_symm_comp]
  obtain ⟨F, hF⟩ := hx n (b ≫ q) hb'
  obtain ⟨L, hL, _⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fullInclusion_extension A D P (SSet.boundary (n + 1)).ι
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundary_vertices_surjective n) b F hF
  exact ⟨L, hL⟩

/-- 概要：零複体を含む充満部分圏の零複体の頂点は Terminal 対象。
方針：周囲の零複体の Terminal 性を包含で反映する。
規約：HTT §1.2.12。使われ方：Semifree などの dg nerve の零対象。 -/
lemma isTerminalVertex_full_zero (P : Complex A → Prop) (hzero : P (0 : Complex A)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (DGFullSubcategory (Complex A) P))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (⟨0, hzero⟩ : DGFullSubcategory (Complex A) P)) := by
  apply isTerminalVertex_of_fullInclusion A (Complex A) P
  have hv : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (⟨0, hzero⟩ : DGFullSubcategory (Complex A) P)).map
      (dgFullSubcategoryInclusion A (Complex A) P) = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (0 : Complex A) := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.injective
    rfl
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (Complex A))
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (⟨0, hzero⟩ : DGFullSubcategory (Complex A) P)).map
    (dgFullSubcategoryInclusion A (Complex A) P))
  rw [hv]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.isTerminalVertex_zero A

/-- 概要：充満 dg 部分圏の包含は Initial 頂点の充填条件を反映する。
方針：周囲の境界充填を、全頂点を覆う境界に沿って部分圏へ持ち上げる。
規約：HTT §1.2.12。使われ方：零対象の Initial 性を部分圏へ戻す。 -/
lemma isInitialVertex_of_fullInclusion (D : Type v) [DGCategory A D] (P : D → Prop)
    (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (DGFullSubcategory D P)) _⦋0⦌)
    (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion A D P)).app _ x)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex x := by
  intro n b hb
  let q := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion A D P)
  have hb' : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (0) ≫ (b ≫ q) =
      SSet.yonedaEquiv.symm (q.app _ x) := by
    rw [← Category.assoc, hb, SSet.yonedaEquiv_symm_comp]
  obtain ⟨F, hF⟩ := hx n (b ≫ q) hb'
  obtain ⟨L, hL, _⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fullInclusion_extension A D P (SSet.boundary (n + 1)).ι
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundary_vertices_surjective n) b F hF
  exact ⟨L, hL⟩

/-- 概要：零複体を含む充満部分圏の零複体の頂点は Initial 対象。
方針：周囲の零複体の Initial 性を包含で反映する。
規約：HTT §1.2.12。使われ方：Semifree などの dg nerve の零対象。 -/
lemma isInitialVertex_full_zero (P : Complex A → Prop) (hzero : P (0 : Complex A)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (DGFullSubcategory (Complex A) P))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (⟨0, hzero⟩ : DGFullSubcategory (Complex A) P)) := by
  apply isInitialVertex_of_fullInclusion A (Complex A) P
  have hv : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (⟨0, hzero⟩ : DGFullSubcategory (Complex A) P)).map
      (dgFullSubcategoryInclusion A (Complex A) P) = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (0 : Complex A) := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.injective
    rfl
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (Complex A))
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (⟨0, hzero⟩ : DGFullSubcategory (Complex A) P)).map
    (dgFullSubcategoryInclusion A (Complex A) P))
  rw [hv]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.isInitialVertex_zero A

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
