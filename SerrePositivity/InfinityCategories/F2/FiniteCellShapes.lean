module

public import Mathlib.AlgebraicTopology.SimplicialSet.Skeleton
public import Mathlib.AlgebraicTopology.SimplicialSet.Finite
public import Mathlib.AlgebraicTopology.SimplicialSet.Monomorphisms

/-!
概要：有限形状のセル付着の各添字が有限で、骨格が有限段で全形状に到達することを示す。
方針：非退化単体の有限性と次元上界を使い、元の骨格と相対セルを扱う。
規約：元の形状・付着順を保持。使われ方：一般 coherent 図式の有限極限交換の帰納。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 次元の上界までの骨格は元の全形状そのものである。 -/
lemma skeleton_eq_top_of_dimension (X : SSet.{u}) (d : ℕ) [X.HasDimensionLT d] :
    X.skeleton d = ⊤ := by
  apply (Subcomplex.eq_top_iff_of_hasDimensionLT _ d).mpr
  intro i hi x hx
  exact X.mem_skeleton x hi

/-- 有限形状の骨格は有限段で元の全形状に到達する。 -/
lemma finiteSkeleton_exists_top (X : SSet.{u}) [X.Finite] : ∃ d, X.skeleton d = ⊤ := by
  obtain ⟨d, hd⟩ := X.hasDimensionLT_of_finite
  exact ⟨d, skeleton_eq_top_of_dimension X d⟩

/-- 有限な標的の相対セル付着の各次元の添字は有限。 -/
instance finiteCellShapeIndex {E X : SSet.{u}} [X.Finite] (i : E ⟶ X) (d : ℕ) :
    Finite (SSet.relativeCellComplexOfMono.Cell i d) :=
  Finite.of_injective
    (fun c => (⟨c.simplex, c.nonDegenerate⟩ : X.nonDegenerate d)) (by
      intro a b h
      apply SSet.relativeCellComplexOfMono.Cell.ext
      exact congrArg Subtype.val h)

/-- 次元上界以降に付着する相対セルは存在しない。 -/
lemma finiteCellShapeIndex_isEmpty {E X : SSet.{u}} (i : E ⟶ X)
    (d n : ℕ) [X.HasDimensionLT d] (hn : d ≤ n) :
    IsEmpty (SSet.relativeCellComplexOfMono.Cell i n) :=
  ⟨fun c => (Nat.not_lt_of_ge hn) (X.dim_lt_of_nonDegenerate ⟨c.simplex, c.nonDegenerate⟩ d)⟩

/-- 有限な標的の相対骨格も有限段で元の全形状に到達する。 -/
lemma finiteRelativeSkeleton_exists_top {E X : SSet.{u}} [X.Finite] (i : E ⟶ X) :
    ∃ d, SSet.skeletonOfMono i d = ⊤ := by
  obtain ⟨d, hd⟩ := finiteSkeleton_exists_top X
  exact ⟨d, by simp only [SSet.skeletonOfMono, OrderHom.coe_mk, hd, sup_top_eq]⟩

/-- 元のセル付着の境界の和から単体の和への射は単射。 -/
lemma finiteCellShapeAttachment_mono {E X : SSet.{u}} (i : E ⟶ X) (n : ℕ) :
    Mono (SSet.relativeCellComplexOfMono.l i n) := by
  infer_instance

end SerrePositivity.InfinityCategories.F2
