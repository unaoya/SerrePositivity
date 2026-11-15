module

public import SerrePositivity.AlgebraicGeometry.AffineHomClosedLimitDescent
public import SerrePositivity.AlgebraicGeometry.AffineHomGeneralLimitDescent

/-!
概要：qcqs な局所有限型の射の極限での閉埋め込み性を、ある有限段へ降ろす。
方針：まず affine 性を降ろし、その段以降の有限被覆の閉埋め込み性の降下を使う。
規約：Stacks 01ZP。基底の Noether 性や遷移の忠実平坦性は要求しない。
使われ方：一般の固有性・分離性の Noether 近似で必要な閉埋め込み性の降下。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u
attribute [local instance] IsCofiltered.isConnected

/-- 指定された合成の底変換と二段の底変換で、閉埋め込み性は同値。 -/
theorem isClosedImmersion_pullback_snd_composite_iff
    {X S T V : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) (h : V ⟶ T)
    (b : V ⟶ S) (hb : h ≫ g = b) :
    IsClosedImmersion (pullback.snd f b) ↔
      IsClosedImmersion (pullback.snd (pullback.snd f g) h) := by
  let sq := isPullback_pullbackCompositeMap f g h b hb
  constructor
  · intro H
    letI := H
    have H' : IsClosedImmersion (sq.isoPullback.inv ≫ pullback.snd f b) := inferInstance
    simpa only [IsPullback.isoPullback_inv_snd] using H'
  · intro H
    letI := H
    have H' : IsClosedImmersion
        (sq.isoPullback.hom ≫ pullback.snd (pullback.snd f g) h) := inferInstance
    simpa only [IsPullback.isoPullback_hom_snd] using H'

/-- qcqs・局所有限型の射の極限での閉埋め込み性は、ある後段へ降りる（Stacks 01ZP）。 -/
theorem exists_closedImmersion_pullback_of_isLimit
    {J : Type u} [SmallCategory J] [IsCofiltered J]
    (D : J ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {j k} (a : j ⟶ k), IsAffineHom (D.map a)]
    [∀ j, CompactSpace (D.obj j)] [∀ j, QuasiSeparatedSpace (D.obj j)]
    {i : J} {X : Scheme.{u}} (f : X ⟶ D.obj i)
    [QuasiCompact f] [QuasiSeparated f] [LocallyOfFiniteType f]
    [IsClosedImmersion (pullback.snd f (c.π.app i))] :
    ∃ (j : J) (a : j ⟶ i), IsClosedImmersion (pullback.snd f (D.map a)) := by
  obtain ⟨j, a, ha⟩ := exists_affineHom_pullback_of_isLimit D c hc f
  let p := pullback.snd f (D.map a)
  letI : IsAffineHom p := ha
  let B := Over.post D ⋙ Over.forget (D.obj j)
  let cb := (Over.forget (D.obj j)).mapCone ((Over.conePost D j).obj c)
  have hb : IsLimit cb :=
    isLimitOfPreserves (Over.forget (D.obj j)) (Over.isLimitConePost j hc)
  haveI {k l : Over j} (g : k ⟶ l) : IsAffineHom (B.map g) := by
    change IsAffineHom (D.map g.left)
    infer_instance
  let o : Over j := Over.mk (𝟙 j)
  haveI : CompactSpace (B.obj o) := by dsimp [B, o]; infer_instance
  haveI : LocallyOfFiniteType p := by dsimp [p]; infer_instance
  haveI : IsClosedImmersion (pullback.snd p (cb.π.app o)) :=
    (isClosedImmersion_pullback_snd_composite_iff f (D.map a) (c.π.app j)
      (c.π.app i) (c.w a)).mp inferInstance
  obtain ⟨k, g, hk⟩ := exists_closedImmersion_pullback_of_isLimit_of_isAffineHom B cb hb (i := o) p
  change IsClosedImmersion (pullback.snd p (D.map g.left)) at hk
  refine ⟨k.left, g.left ≫ a, ?_⟩
  exact (isClosedImmersion_pullback_snd_composite_iff f (D.map a) (D.map g.left)
    (D.map (g.left ≫ a)) (D.map_comp g.left a).symm).mpr hk

end SerrePositivity.AlgebraicGeometry
