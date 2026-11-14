module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Triangles.DGPretriangulatedTria
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Pretriangulated.DGPretriangulatedStability
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGQuotientNerve
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparison.Equivalence

/-! # 局所 K-flat な dg 商の前三角性と安定性

概要：前三角 dg 圏の局所 K-flat な path 商は前三角で、その実 nerve は安定。
方針：tria の Verdier 比較で全対象の代表可能性を送り、有限 cell の K(D) へ戻す。
規約：局所 K-flat 性を明示し、未分解の商へ無条件に適用しない。使われ方：β3。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded DGQuotient
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 局所 K-flat な前三角 dg 圏の商の tria の全対象は代表対象と同型。 -/
lemma dgQuotientTria_isRepresentable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]
    (S : Set D) (h : localKFlat A D S) (Y : TriaCategory A (QuotientObject D S)) :
    ∃ x : QuotientObject D S, Nonempty (Y ≅ triaRepresentable A (QuotientObject D S) x) := by
  let E := localQuotientTriaEquivalence A D S h
  let Z := E.inverse.obj Y
  let Q := triaQuotient A D S
  obtain ⟨x, ⟨e⟩⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTria_isRepresentable A D (Q.objPreimage Z)
  refine ⟨⟨x⟩, ⟨(E.counitIso.app Y).symm ≪≫
    E.functor.mapIso (Q.objObjPreimageIso Z).symm ≪≫
    E.functor.mapIso (Q.mapIso e) ≪≫ ?_⟩⟩
  exact localQuotientTriaRepresentableIso A D S x

/-- tria の代表可能性を K(D/S) へ戻すと実 dg 商の前三角性を得る。 -/
lemma dgQuotient_isDGPretriangulated [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]
    (S : Set D) (h : localKFlat A D S) : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A (QuotientObject D S) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.isDGPretriangulated_of_tria_representable A (QuotientObject D S)
    (dgQuotientTria_isRepresentable A D S h)

/-- 局所 K-flat な前三角 dg 圏の実商 nerve は安定。 -/
theorem dgQuotientNerve_isStable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]
    (S : Set D) (h : localKFlat A D S) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerve A D S) := by
  let := dgQuotient_isDGPretriangulated A D S h
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Pretriangulated.dgNerve_isStable_of_pretriangulated A (QuotientObject D S)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
