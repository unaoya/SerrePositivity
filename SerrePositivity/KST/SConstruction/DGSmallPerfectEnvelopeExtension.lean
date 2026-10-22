module
public import SerrePositivity.KST.SConstruction.DGSmallPerfectEnvelope
public import SerrePositivity.KST.SConstruction.PerfectDGExtension

/-! # 元の実 Perf 延長を保つ小さい dg 模型間の厳密射
概要：始域の実対象の延長像を終域の小模型へ加え、元の実延長を厳密に制限する。
方針：小さい始域全体で添字付けた実延長像を使い、D の充満部分圏制限を適用する。
規約：同型な代表への選び直しをしない。使われ方：実 LT 四角形の厳密 dg 入力。
-/
@[expose] public section
noncomputable section
universe u v w z
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (E : Type w) [DGCategory R E] [Small.{u} E]
  (J : Type z) (X : J → PerfectDGModule R D) (F : DGFunctor R D E)
local notation "C" => DGSmallPerfectEnvelope R D J X

/-- 小さい始域の各実対象を元の実 Perf 延長で送った、そのままの像族。 -/
def dgSmallPerfectEnvelopeExtensionFamily (a : C) : PerfectDGModule R E :=
  (perfectDGExtension R D E F).obj a.val

/-- 元の実延長像を全て含む、同じ終域 Perf の具体的小模型。 -/
abbrev DGSmallPerfectEnvelopeExtensionTarget :=
  DGSmallPerfectEnvelope R E (C) (dgSmallPerfectEnvelopeExtensionFamily R D E J X F)

/-- 始域の指定族が小さければ、実延長像を含む終域も実際に小さい。 -/
instance dgSmallPerfectEnvelopeExtensionTargetSmall [Small.{u} J] :
    Small.{u} (DGSmallPerfectEnvelopeExtensionTarget R D E J X F) :=
  dgSmallPerfectEnvelopeSmall R E (C) (dgSmallPerfectEnvelopeExtensionFamily R D E J X F)

/-- 元の実 Perf 延長を、指定した実像を含む終域へ厳密に制限する。 -/
def dgSmallPerfectEnvelopeExtension :
    DGFunctor R (C) (DGSmallPerfectEnvelopeExtensionTarget R D E J X F) :=
  (perfectDGExtension R D E F).restrict
    (dgSmallPerfectEnvelopeObjects R D J X)
    (dgSmallPerfectEnvelopeObjects R E (C) (dgSmallPerfectEnvelopeExtensionFamily R D E J X F))
    (fun a ha => Or.inr (Or.inl ⟨⟨a, ha⟩, rfl⟩))

/-- 終域への包含の後で、同じ元の実 Perf 延長を対象と全 Hom で厳密に回収する。 -/
lemma dgSmallPerfectEnvelopeExtension_inclusion :
    (dgSmallPerfectEnvelopeExtension R D E J X F).comp
      (dgSmallPerfectEnvelopeInclusion R E (C)
        (dgSmallPerfectEnvelopeExtensionFamily R D E J X F)) =
    (dgSmallPerfectEnvelopeInclusion R D J X).comp (perfectDGExtension R D E F) :=
  DGFunctor.restrict_comp_inclusion (perfectDGExtension R D E F)
    (dgSmallPerfectEnvelopeObjects R D J X)
    (dgSmallPerfectEnvelopeObjects R E (C) (dgSmallPerfectEnvelopeExtensionFamily R D E J X F))
    (fun a ha => Or.inr (Or.inl ⟨⟨a, ha⟩, rfl⟩))

end SerrePositivity.KST.SConstruction
