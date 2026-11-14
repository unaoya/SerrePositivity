module

public import SerrePositivity.BhattScholze.Prismatic.CechAlexander.Envelopes.AffineEnvelopeMaps
import all SerrePositivity.BhattScholze.Prismatic.CechAlexander.Envelopes.AffineEnvelopeMaps

/-!
# 有限 affine 枠の変数像による持ち上げ

## 概要
有限 affine 枠の各変数に、剰余で頂点によらない像を指定して包からの射を作る。

## 方針
完備自由 δ 環の普遍性で変数の写像を延長する。
頂点差は標的のイデアルに入るので、prismatic envelope の普遍性を使う。

## 規約
比較は同じ係数 prism の上で行い、標的の変数像に δ が零であることは課さない。

## 使われ方
BS 著者版 Remark 4.19 の枠の比較と余単体ホモトピー。
-/

public noncomputable section

universe u

namespace SerrePositivity.BhattScholze.Prismatic.AffineEnvelopeTerm

set_option backward.isDefEq.respectTransparency false

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {P : OrientedPrism p A}
variable {r n : ℕ} {κ : Cardinal.{u}} (X : AffineEnvelopeTerm P r n κ)
variable {R : Type u} [CommRing R] (T : OrientedPrism p R) (b : OrientedPrism.Hom P T)
variable (v : Fin r → Fin (n + 1) → R)
variable (hv : ∀ j i, Ideal.Quotient.mk T.ideal (v j i) = Ideal.Quotient.mk T.ideal (v j 0))

include hv in
/-- 剰余で頂点によらない変数像は、有限 affine 枠の包からの一意な δ 射を定める。 -/
theorem existsUnique_liftVariables :
    ∃! f : X.X.B →+* R,
      X.X.Q.deltaStructure.IsDeltaHom T.deltaStructure f ∧
      f.comp X.X.toHom.toRingHom = b.toRingHom ∧
      ∀ j i, f (X.η (affineVariable P r n j i)) = v j i := by
  let S := AffineIndex.{u} r n
  let w (s : S) := v s.down.1 s.down.2
  obtain ⟨g, hg, hgu⟩ := existsUnique_completedFreeDeltaHom P S T.deltaStructure
    b.toRingHom b.map_delta T.complete_p b.isModuleComplete_map_generator w
  have hgen : P.ideal ≤ T.ideal.comap (g.comp (completedFreeDeltaBase P S)) := by
    rw [hg.2.1]
    exact b.ideal_le
  have hI : (affineDifferenceIdeal P r n).map g ≤ T.ideal := by
    rw [Ideal.map_le_iff_le_comap, affineDifferenceIdeal, Ideal.span_le]
    rintro a (ha | ⟨⟨j, i⟩, rfl⟩)
    · obtain rfl := ha
      change (g.comp (completedFreeDeltaBase P S)) P.generator ∈ T.ideal
      exact hgen (Ideal.subset_span (Set.mem_singleton _))
    · change g (affineVariable P r n j i - affineVariable P r n j 0) ∈ T.ideal
      rw [map_sub, affineVariable_eq, affineVariable_eq, hg.2.2, hg.2.2]
      exact Ideal.Quotient.eq.mp (hv j i)
  obtain ⟨f, hf, hfu⟩ := X.envelope.lift T g hg.1 hgen hI
  refine ⟨f, ⟨hf.1, ?_, ?_⟩, ?_⟩
  · rw [← X.base_eq, ← RingHom.comp_assoc, hf.2, hg.2.1]
  · intro j i
    change (f.comp X.η) (affineVariable P r n j i) = _
    rw [hf.2, affineVariable_eq, hg.2.2]
  intro f' hf'
  apply hfu
  refine ⟨hf'.1, hgu _ ⟨hf'.1.comp X.envelope.isDeltaHom, ?_, ?_⟩⟩
  · rw [RingHom.comp_assoc, X.base_eq, hf'.2.1]
  · rintro ⟨⟨j, i⟩⟩
    exact hf'.2.2 j i

end SerrePositivity.BhattScholze.Prismatic.AffineEnvelopeTerm
