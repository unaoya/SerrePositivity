module

public import SerrePositivity.AlgebraicGeometry.DiagonalClosedBaseChange
public import SerrePositivity.AlgebraicGeometry.FlatStageClosedImmersionLimit
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
概要：qcqs な射の極限での分離性を、ある有限段の実際の底変換へ降ろす。
方針：二重交叉を極限の頂点に保ち、対角の閉埋め込み性を有限段へ降ろす。
規約：Stacks 01ZQ。元の射の局所有限型性・基底の Noether 性を仮定しない。
使われ方：一般の固有性と有限表示の固有模型の Noether 近似。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u

/-- qcqs な射の極限での分離性は、ある後段へ降りる（Stacks 01ZQ）。 -/
theorem exists_isSeparated_pullback_of_isLimit
    {J : Type u} [SmallCategory J] [IsCofiltered J]
    (D : J ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {j k} (a : j ⟶ k), IsAffineHom (D.map a)]
    [∀ j, CompactSpace (D.obj j)] [∀ j, QuasiSeparatedSpace (D.obj j)]
    {i : J} {X : Scheme.{u}} (f : X ⟶ D.obj i)
    [QuasiCompact f] [QuasiSeparated f]
    [IsSeparated (pullback.snd f (c.π.app i))] :
    ∃ (j : J) (a : j ⟶ i), IsSeparated (pullback.snd f (D.map a)) := by
  let g := c.π.app i
  let a := pullback.fst f g
  let p := pullback.snd f g
  have h : IsPullback a p f g := IsPullback.of_hasPullback f g
  let r := pullback.fst f f ≫ f
  let b := cartesianPullbackMap p p f f g a a h h
  let x := pullback.fst p p ≫ p
  have hpair : IsPullback b x r g := isPullback_cartesianPullbackMap p p f f g a a h h
  haveI : QuasiCompact r := by dsimp [r]; infer_instance
  haveI : QuasiSeparated r := by dsimp [r]; infer_instance
  haveI : LocallyOfFiniteType (pullback.diagonal f) := by
    haveI : LocallyOfFiniteType (pullback.diagonal f ≫ pullback.fst f f) := by
      rw [pullback.diagonal_fst]
      infer_instance
    exact locallyOfFiniteType_of_comp (pullback.diagonal f) (pullback.fst f f)
  haveI : IsClosedImmersion (pullback.snd (pullback.diagonal f) b) :=
    isClosedImmersion_diagonal_pullback_of_isSeparated a p f g h
  haveI : IsClosedImmersion (pullback.snd (pullback.diagonal f) (b ≫ 𝟙 _)) :=
    isClosedImmersion_pullback_snd_of_composite (pullback.diagonal f) b (𝟙 _) (b ≫ 𝟙 _) (by simp)
  obtain ⟨j, hj⟩ := exists_closedImmersion_flatStageProjection_of_isLimit D c hc i b x r hpair
    (𝟙 _) (pullback.diagonal f)
  letI : IsClosedImmersion (pullback.fst
      (pullback.snd (D.map j.hom) (pullback.fst f f ≫ f) ≫ 𝟙 _)
      (pullback.diagonal f)) := hj
  haveI : IsSeparated (pullback.fst (D.map j.hom) f) :=
    isSeparated_of_closed_diagonal_stage (pullback.snd (D.map j.hom) f)
      (pullback.fst (D.map j.hom) f) f (D.map j.hom)
      (IsPullback.of_hasPullback (D.map j.hom) f).flip
  refine ⟨j.left, j.hom, ?_⟩
  have H : IsSeparated ((pullbackSymmetry f (D.map j.hom)).hom ≫
      pullback.fst (D.map j.hom) f) := inferInstance
  simpa using H

end SerrePositivity.AlgebraicGeometry
