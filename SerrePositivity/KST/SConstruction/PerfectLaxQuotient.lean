module
public import SerrePositivity.KST.SConstruction.PerfectLaxCategory
public import SerrePositivity.KST.SConstruction.PerfectVerdierSequence
public import SerrePositivity.InfinityCategories.Derived.Lax.LaxQuotientLegComparison

/-! # 元の lax pullback の商と冪等完備化の入力
概要：実 Verdier 商とその完備化を保持し、Cat^perf の列と LT の二脚を定義する。
方針：未完備な商の二脚を、元の完備化関手と合成する。
規約：商と完備化の存在は入力。商自体の完備性は要求しない。使われ方：dg の ⊙ 提示。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.InfinityCategories LocalizingInvariants
open F2.Idempotent

/-- 元の lax pullback の実商と、その実冪等完備化を保持する入力。 -/
structure PerfectLaxQuotient {C D B : StableCategory.{u}}
    (p : ExactMap C B) (q : ExactMap D B) where
  left : StableCategory.{u}
  rawQuotient : StableCategory.{u}
  right : StableCategory.{u}
  inclusion : ExactMap left (laxCategory p q)
  rawProjection : ExactMap (laxCategory p q) rawQuotient
  isVerdier : IsVerdierSequence inclusion rawProjection
  left_complete : IsIdempotentComplete left.obj
  c_complete : IsIdempotentComplete C.obj
  d_complete : IsIdempotentComplete D.obj
  completion : ExactMap rawQuotient right
  isCompletion : IsIdempotentCompletion completion.hom

namespace PerfectLaxQuotient
variable {C D B : StableCategory.{u}} {p : ExactMap C B} {q : ExactMap D B}
  (d : PerfectLaxQuotient p q)

include d in
/-- 元の二入力から証明した、同じ lax pullback の完備性。 -/
lemma middle_complete : IsIdempotentComplete (laxCategory p q).obj :=
  perfectLaxCategory_isIdempotentComplete p q d.c_complete d.d_complete

/-- 同じ元の完備化先の完備性。 -/
lemma right_complete : IsIdempotentComplete d.right.obj := d.isCompletion.1

/-- 元の実商・完備化をそのまま持つ Cat^perf の提示列。 -/
def sequence : PerfectVerdierSequence.{u} where
  verdier := ⟨d.left, laxCategory p q, d.rawQuotient,
    d.inclusion, d.rawProjection, d.isVerdier⟩
  left_complete := d.left_complete
  middle_complete := d.middle_complete
  right := d.right
  completion := d.completion
  isCompletion := d.isCompletion

/-- C 側の元の射影を含む、左端からの完全関手。 -/
def cSource : ExactMap d.left C :=
  ⟨d.inclusion.hom ≫ (laxFst p q).hom, isExactFunctor_comp _ _⟩

/-- D 側の元の射影を含む、左端からの完全関手。 -/
def dSource : ExactMap d.left D :=
  ⟨d.inclusion.hom ≫ (laxSnd p q).hom, isExactFunctor_comp _ _⟩

/-- 未完備な商の元の C 側の脚を、同じ完備化へ送る。 -/
def cLeg : ExactMap C d.right :=
  ⟨(laxQuotientCLeg p q d.rawProjection).hom ≫ d.completion.hom, isExactFunctor_comp _ _⟩

/-- 未完備な商の元の D 側の脚を、同じ完備化へ送る。 -/
def dLeg : ExactMap D d.right :=
  ⟨(laxQuotientDLeg p q d.rawProjection).hom ≫ d.completion.hom, isExactFunctor_comp _ _⟩

/-- 提示列の包含は元の包含そのもの。 -/
lemma sequence_inclusion : d.sequence.verdier.inclusion = d.inclusion := rfl

/-- 提示列の射影は、元の実商射と完備化の合成そのもの。 -/
lemma sequence_projection : d.sequence.projection.hom =
    d.rawProjection.hom ≫ d.completion.hom := rfl

end PerfectLaxQuotient
end SerrePositivity.KST.SConstruction
