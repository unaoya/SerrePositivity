module

public import SerrePositivity.AlgebraicGeometry.AffineCartesianClosedLimit
public import SerrePositivity.AlgebraicGeometry.CompositeStageBaseChangeLimit
public import SerrePositivity.AlgebraicGeometry.PullbackComparison

/-!
概要：固定した affine な射の、極限での閉埋め込み性を有限段の底変換へ降ろす。
方針：元の頂点を保つ実際の底変換の極限と、その射影の自然変換を使う。
規約：Stacks 01ZP の affine な場合。元の基底の Noether 性は仮定しない。
使われ方：一般の閉埋め込み性の有限 affine 被覆上での降下。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u
attribute [local instance] IsCofiltered.isConnected

/-- 合成係数の底変換図式から元の基底への第一射影の自然変換。 -/
def compositeStageBaseProjection {J : Type u} [SmallCategory J]
    (D : J ⥤ Scheme.{u}) (i : J) {S X : Scheme.{u}}
    (γ : D.obj i ⟶ S) (p : X ⟶ S) :
    compositeStageBaseChangeDiagram D i γ p ⟶ Over.post D ⋙ Over.forget (D.obj i) where
  app j := pullback.fst (D.map j.hom ≫ γ) p
  naturality j k a := (isPullback_compositeStageBaseChangeDiagram_map D i γ p a).w

/-- affine な射の極限での閉埋め込み性を、ある後段の実際の底変換へ降ろす。 -/
theorem exists_closedImmersion_pullback_of_isLimit_of_affine
    {J : Type u} [SmallCategory J] [IsCofiltered J]
    (D : J ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ j, IsAffine (D.obj j)] {i : J} {X : Scheme.{u}} [IsAffine X]
    (p : X ⟶ D.obj i) [LocallyOfFiniteType p]
    [IsClosedImmersion (pullback.snd p (c.π.app i))] :
    ∃ (j : J) (a : j ⟶ i), IsClosedImmersion (pullback.snd p (D.map a)) := by
  let E := compositeStageBaseChangeDiagram D i (𝟙 _) p
  let B := Over.post D ⋙ Over.forget (D.obj i)
  let cb := (Over.forget (D.obj i)).mapCone ((Over.conePost D i).obj c)
  have hb : IsLimit cb :=
    isLimitOfPreserves (Over.forget (D.obj i)) (Over.isLimitConePost i hc)
  let ce := compositeStageBaseChangeConeWithPoint D c i (𝟙 _) p (c.π.app i) (by simp)
  have he : IsLimit ce :=
    isLimit_compositeStageBaseChangeConeWithPoint D c hc i (𝟙 _) p (c.π.app i) (by simp)
  let τ := compositeStageBaseProjection D i (𝟙 _) p
  haveI (j : Over i) : IsAffine (B.obj j) := by dsimp [B]; infer_instance
  haveI (j : Over i) : IsAffine (E.obj j) := by dsimp [E, compositeStageBaseChangeDiagram]; infer_instance
  let o : Over i := Over.mk (𝟙 i)
  haveI : LocallyOfFiniteType (τ.app o) := by
    dsimp [τ, compositeStageBaseProjection]
    infer_instance
  obtain ⟨j, a, hj⟩ := exists_closedImmersion_stage_of_affine_cartesian_limit B E τ cb ce hb he
    (pullback.snd p (c.π.app i))
    (fun j ↦ compositeStageBaseChangeConeWithPoint_π_fst D c i (𝟙 _) p (c.π.app i) (by simp) j)
    o (fun j a ↦ isPullback_compositeStageBaseChangeDiagram_map D i (𝟙 _) p a)
  change IsClosedImmersion (pullback.fst (D.map j.hom ≫ 𝟙 _) p) at hj
  letI : IsClosedImmersion (pullback.fst (D.map j.hom ≫ 𝟙 _) p) := hj
  haveI : IsClosedImmersion (pullback.fst (D.map j.hom) p) := by
    have H : IsClosedImmersion
        ((pullback.congrHom (Category.comp_id (D.map j.hom)) (rfl : p = p)).inv ≫
          pullback.fst (D.map j.hom ≫ 𝟙 _) p) := inferInstance
    simpa only [pullbackCongrHom_inv_fst] using H
  refine ⟨j.left, j.hom, ?_⟩
  have h : IsClosedImmersion ((pullbackSymmetry p (D.map j.hom)).hom ≫
      pullback.fst (D.map j.hom) p) := inferInstance
  simpa using h

end SerrePositivity.AlgebraicGeometry
