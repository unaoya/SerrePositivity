module

public import SerrePositivity.AlgebraicGeometry.ClopenLimitDescent
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Restrict

/-!
概要：準コンパクトな開包含の閉埋め込み性を有限段へ降ろす。
方針：底変換の像を開の逆像で表し、その閉性を共通段へ移す。
規約：Stacks 01ZP の開包含の場合。C04 の一般の閉埋め込み性の降下は別に残る。
使われ方：G2 の射の性質の有限段への移送。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits Topology
universe u

/-- 準コンパクト開の包含が極限で閉埋め込みなら、後のある段でも実際に閉埋め込み。 -/
theorem exists_closedImmersion_open_pullback_of_isLimit
    {J : Type u} [SmallCategory J] [IsCofiltered J]
    (D : J ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    {i : J} (U : (D.obj i).Opens) (hU : IsCompact (U : Set (D.obj i)))
    [IsClosedImmersion (pullback.snd U.ι (c.π.app i))] :
    ∃ (j : J) (a : j ⟶ i), IsClosedImmersion (pullback.snd U.ι (D.map a)) := by
  have hclosed : IsClosed ((c.π.app i ⁻¹ᵁ U : c.pt.Opens) : Set c.pt) := by
    simpa only [Scheme.Pullback.range_snd, Scheme.Opens.range_ι, Scheme.Hom.coe_preimage] using
      (pullback.snd U.ι (c.π.app i)).isClosedEmbedding.isClosed_range
  obtain ⟨j, a, ha⟩ := exists_closed_open_preimage_of_isLimit D c hc U hU hclosed
  refine ⟨j, a, IsClosedImmersion.of_isPreimmersion _ ?_⟩
  simpa only [Scheme.Pullback.range_snd, Scheme.Opens.range_ι, Scheme.Hom.coe_preimage] using ha

end SerrePositivity.AlgebraicGeometry
