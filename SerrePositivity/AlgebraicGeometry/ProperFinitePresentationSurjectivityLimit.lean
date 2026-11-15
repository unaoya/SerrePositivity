module

public import SerrePositivity.AlgebraicGeometry.ProperSurjectivityApproximation
public import SerrePositivity.AlgebraicGeometry.ConstructibleCompactness

/-!
概要：固有・局所有限表示な射の全射性を、qcqs な逆極限から有限段へ降ろす。
方針：Chevalley の構成可能な像の補開の準コンパクト性と、逆像が空になる有限段を使う。
規約：Stacks 32.8.15 (081C)。Noether な段や忠実平坦な遷移は要求しない。
使われ方：A07 の固有側の全射性の移送。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits Topology
universe u

set_option backward.isDefEq.respectTransparency false in
/-- 固有・局所有限表示な射の底変換が極限上で全射なら、ある有限段でも全射。 -/
theorem exists_surjective_proper_pullback_of_isLimit
    {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
    [∀ {i j} (a : i ⟶ j), IsAffineHom (D.map a)]
    {c : Cone D} (hc : IsLimit c) {i : I}
    [CompactSpace (D.obj i)] [QuasiSeparatedSpace (D.obj i)]
    {X : Scheme.{u}} (f : X ⟶ D.obj i) [IsProper f] [LocallyOfFinitePresentation f]
    [Surjective (pullback.snd f (c.π.app i))] :
    ∃ (j : I) (a : j ⟶ i), Surjective (pullback.snd f (D.map a)) := by
  let U : (D.obj i).Opens := ⟨(Set.range f)ᶜ, f.isClosedMap.isClosed_range.isOpen_compl⟩
  have hempty : c.π.app i ⁻¹ᵁ U = ⊥ := by
    ext x
    change (c.π.app i x ∉ Set.range f) ↔ False
    rw [← Set.mem_preimage, ← Scheme.Pullback.range_snd, Set.range_eq_univ.mpr
      (pullback.snd f (c.π.app i)).surjective]
    simp
  obtain ⟨j, a, ha⟩ := exists_preimage_eq_bot_of_isLimit D hc U
    (isCompact_of_isConstructible_scheme (by
      simpa only [U, Set.image_univ] using
        (f.isConstructible_image IsConstructible.univ).compl)) hempty
  refine ⟨j, a, ⟨?_⟩⟩
  rw [← Set.range_eq_univ, Scheme.Pullback.range_snd, ← Set.compl_empty_iff]
  exact congrArg (fun V : (D.obj j).Opens => V.carrier) ha


end SerrePositivity.AlgebraicGeometry
