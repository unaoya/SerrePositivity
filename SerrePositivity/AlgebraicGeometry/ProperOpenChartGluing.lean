module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Restrict

/-!
概要：指定した開部分が標的のチャートの逆像なら、局所の固有性を全体に移す。
方針：各正方形を実際の pullback と示し、固有性の標的局所性を適用する。
規約：元の基底への忠実平坦性を要求しない。
使われ方：C06 の貼り合わせた射の固有性と全射性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits TopologicalSpace
universe u v

/-- 指定した開部分がチャートの逆像であるとき、局所の固有性は全体の固有性を与える。 -/
theorem isProper_of_open_chart_ranges {T X : Scheme.{u}} {I : Type v}
    (a : T ⟶ X) (U : I → X.Opens) (hcover : (⨆ i, U i) = ⊤)
    (V : I → Scheme.{u}) (c : ∀ i, V i ⟶ T) [∀ i, IsOpenImmersion (c i)]
    (r : ∀ i, V i ⟶ (U i).toScheme) (hr : ∀ i, IsProper (r i))
    (hcomm : ∀ i, c i ≫ a = r i ≫ (U i).ι)
    (hrange : ∀ i, Set.range (c i) = (a ⁻¹ᵁ U i : Set T)) : IsProper a := by
  let 𝒰 : X.OpenCover.{v} := {
    I₀ := I
    X i := (U i).toScheme
    f i := (U i).ι
    mem₀ := by
      rw [Scheme.presieve₀_mem_precoverage_iff]
      refine ⟨fun x ↦ ?_, inferInstance⟩
      have hx : x ∈ (⨆ i, U i) := by rw [hcover]; trivial
      obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
      exact ⟨i, ⟨x, hi⟩, rfl⟩ }
  apply IsZariskiLocalAtTarget.of_openCover 𝒰
  intro i
  have hpb : IsPullback (r i) (c i) (U i).ι a := by
    apply IsOpenImmersion.isPullback _ _ _ _ (hcomm i)
    rw [Scheme.Opens.opensRange_ι]
    apply Opens.ext
    exact (hrange i).symm
  have hh : IsProper (hpb.flip.isoPullback.hom ≫ pullback.snd a (U i).ι) := by
    rw [hpb.flip.isoPullback_hom_snd]
    exact hr i
  exact (MorphismProperty.cancel_left_of_respectsIso (P := @IsProper)
    (f := hpb.flip.isoPullback.hom) _).mp hh

/-- 固有な射は、稠密な合成を持てば全射。 -/
theorem surjective_of_proper_of_dense_comp {W T X : Scheme.{u}}
    (w : W ⟶ T) (a : T ⟶ X) [IsProper a] [IsDominant (w ≫ a)] :
    Surjective a := by
  haveI : IsDominant a := IsDominant.of_comp w a
  exact surjective_of_isDominant_of_isClosed_range a a.isClosedMap.isClosed_range

end SerrePositivity.AlgebraicGeometry
