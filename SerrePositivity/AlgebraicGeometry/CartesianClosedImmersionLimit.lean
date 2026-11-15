module

public import SerrePositivity.AlgebraicGeometry.ClosedImmersionLimitDescent

/-!
概要：閉埋め込み性の有限段への降下を、指定された Cartesian な自然変換へ移す。
方針：二つの実際の Cartesian 正方形の pullback との同型を使う。
規約：C04 の既存の出口の係数移送。余分な模型の存在は仮定しない。
使われ方：対角の図式と一般の固有性の降下の実際の比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u

/-- 指定された Cartesian な図式の極限射の閉埋め込み性を、ある後段へ降ろす。 -/
theorem exists_closedImmersion_stage_of_cartesian_limit
    {J : Type u} [SmallCategory J] [IsCofiltered J]
    (D E : J ⥤ Scheme.{u}) (τ : E ⟶ D) (c : Cone D) (hc : IsLimit c)
    [∀ {j k} (a : j ⟶ k), IsAffineHom (D.map a)]
    [∀ j, CompactSpace (D.obj j)] [∀ j, QuasiSeparatedSpace (D.obj j)]
    (i : J) [QuasiCompact (τ.app i)] [QuasiSeparated (τ.app i)]
    [LocallyOfFiniteType (τ.app i)]
    {Y : Scheme.{u}} (φ : Y ⟶ c.pt) [IsClosedImmersion φ]
    (a : Y ⟶ E.obj i) (hlimit : IsPullback a φ (τ.app i) (c.π.app i))
    (hcartesian : ∀ (j : J) (f : j ⟶ i),
      IsPullback (E.map f) (τ.app j) (τ.app i) (D.map f)) :
    ∃ (j : J) (_ : j ⟶ i), IsClosedImmersion (τ.app j) := by
  haveI : IsClosedImmersion (pullback.snd (τ.app i) (c.π.app i)) := by
    have H : IsClosedImmersion (hlimit.isoPullback.inv ≫ φ) := inferInstance
    simpa only [IsPullback.isoPullback_inv_snd] using H
  obtain ⟨j, f, hj⟩ := exists_closedImmersion_pullback_of_isLimit D c hc (τ.app i)
  letI := hj
  let sq := hcartesian j f
  have H : IsClosedImmersion (sq.isoPullback.hom ≫ pullback.snd (τ.app i) (D.map f)) :=
    inferInstance
  exact ⟨j, f, by simpa only [IsPullback.isoPullback_hom_snd] using H⟩

end SerrePositivity.AlgebraicGeometry
