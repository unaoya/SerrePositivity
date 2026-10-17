module
public import SerrePositivity.DifferentialGraded.Quotient.Universal

/-! # 指定部分集合を対応させる dg 関手の、明示的商への延長 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)
  (S : Set D) (T : Set E) (hF : ∀ d ∈ S, F.obj d ∈ T)

/-- 対象の対応により、標的商の標準 ε を収縮データとして指定する。 -/
def functorContracted : ContractedFunctor A D S (QuotientObject E T) where
  toDGFunctor := F.comp (inclusion A E T)
  homotopy b := epsilonElement A E T ⟨F.obj b.val, hF b.val b.property⟩
  d_homotopy b := differential_epsilonElement A E T ⟨F.obj b.val, hF b.val b.property⟩

/-- 固定した ε を保つ、明示的 dg 商間の実際の関手。 -/
def quotientDGFunctor : DGFunctor A (QuotientObject D S) (QuotientObject E T) :=
  extension A (functorContracted A D E F S T hF)

lemma quotientDGFunctor_obj (x : QuotientObject D S) :
    (quotientDGFunctor A D E F S T hF).obj x = ⟨F.obj x.val⟩ := rfl

/-- 元の dg 圏の包含と、商への延長は厳密に可換する。 -/
lemma quotientDGFunctor_inclusion :
    (inclusion A D S).comp (quotientDGFunctor A D E F S T hF) =
      F.comp (inclusion A E T) :=
  inclusion_comp_extension A (functorContracted A D E F S T hF)

lemma quotientDGFunctor_epsilon (b : S) :
    ((quotientDGFunctor A D E F S T hF).map ⟨b.val⟩ ⟨b.val⟩).f (-1)
        (epsilonElement A D S b) =
      epsilonElement A E T ⟨F.obj b.val, hF b.val b.property⟩ :=
  restrict_extension_homotopy A (functorContracted A D E F S T hF) b
end SerrePositivity.DifferentialGraded.DGQuotient
