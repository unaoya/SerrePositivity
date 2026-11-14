module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
概要：平坦・局所有限表示な射の全射性を、逆極限から有限段へ降ろす。
方針：開像の逆像が極限で全体なら、ある段ですでに全体となる。
規約：Stacks 32.8.15 (081C) の平坦な場合。遷移射の全射性・忠実平坦性は要求しない。
使われ方：A07 の fppf 側の全射性を同じ有限段へそろえる。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u

set_option backward.isDefEq.respectTransparency false in
/-- 平坦・局所有限表示な射の底変換が極限上で全射なら、ある有限段でも全射。 -/
theorem exists_surjective_flat_pullback_of_isLimit
    {J : Type u} [SmallCategory J] [IsCofiltered J]
    (D : J ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i, CompactSpace (D.obj i)] {i : J}
    {Y : Scheme.{u}} (p : Y ⟶ D.obj i)
    [Flat p] [LocallyOfFinitePresentation p] [QuasiCompact p]
    [Surjective (pullback.snd p (c.π.app i))] :
    ∃ (j : J) (a : j ⟶ i), Surjective (pullback.snd p (D.map a)) := by
  let U : (D.obj i).Opens := ⟨Set.range p, p.isOpenMap.isOpen_range⟩
  have hU : c.π.app i ⁻¹ᵁ U = ⊤ := by
    apply SetLike.coe_injective
    change (c.π.app i) ⁻¹' Set.range p = Set.univ
    rw [← Scheme.Pullback.range_snd]
    exact Set.range_eq_univ.mpr (pullback.snd p (c.π.app i)).surjective
  obtain ⟨j, a, ha⟩ := exists_map_eq_top D c hc U hU
  refine ⟨j, a, ⟨?_⟩⟩
  rw [← Set.range_eq_univ, Scheme.Pullback.range_snd]
  exact congrArg (fun V : (D.obj j).Opens ↦ V.carrier) ha

end SerrePositivity.AlgebraicGeometry
