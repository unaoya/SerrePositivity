module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicTopology.CechNerve
public import Mathlib.CategoryTheory.Limits.Opposites

/-!
概要：同じアフィン nerve の広義ファイバー積の大域切断は、元の環の余積を与える。
方針：Γ のアフィン図式の極限保存と反対圏・添字の同値を使う。
規約：元の射影と基底への射を余錐の脚として保持する。
使われ方：アフィン nerve と環の conerve の自然な比較。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
universe u
variable {Y S : Scheme.{u}} (f : Y ⟶ S)

set_option backward.isDefEq.respectTransparency false in
/-- 同じ広義ファイバー積の大域切断を点とする、元の各射影の Γ の余錐。 -/
def affineGammaCechCocone (n : SimplexCategory) :
    Cocone (WidePushoutShape.wideSpan (Scheme.Γ.obj (op S))
      (fun _ : Fin (n.len + 1) ↦ Scheme.Γ.obj (op Y))
      (fun _ ↦ Scheme.Γ.map f.op)) := by
  let D := WidePullbackShape.wideCospan S (fun _ : Fin (n.len + 1) ↦ Y) (fun _ ↦ f)
  let E := widePushoutShapeOp (Fin (n.len + 1)) ⋙ (D ⋙ Scheme.Γ.rightOp).leftOp
  let e : WidePushoutShape.wideSpan (Scheme.Γ.obj (op S))
      (fun _ : Fin (n.len + 1) ↦ Scheme.Γ.obj (op Y))
      (fun _ ↦ Scheme.Γ.map f.op) ≅ E :=
    (WidePushoutShape.diagramIsoWideSpan E).symm
  exact (Cocone.precompose e.hom).obj
    ((coconeLeftOpOfCone (Scheme.Γ.rightOp.mapCone (limit.cone D))).whisker
      (widePushoutShapeOp (Fin (n.len + 1))))

set_option backward.isDefEq.respectTransparency false in
/-- アフィンの同じ図式の極限保存は、同じ大域切断の余錐の普遍性を与える。 -/
def affineGammaCechIsColimit [IsAffine Y] [IsAffine S] (n : SimplexCategory) :
    IsColimit (affineGammaCechCocone f n) := by
  let D := WidePullbackShape.wideCospan S (fun _ : Fin (n.len + 1) ↦ Y) (fun _ ↦ f)
  haveI (j : WidePullbackShape (Fin (n.len + 1))) : IsAffine (D.obj j) := by
    cases j with
    | none => change IsAffine S; infer_instance
    | some j => change IsAffine Y; infer_instance
  have P := isLimitOfPreserves Scheme.Γ.rightOp (limit.isLimit D)
  let E := widePushoutShapeOp (Fin (n.len + 1)) ⋙ (D ⋙ Scheme.Γ.rightOp).leftOp
  let e : WidePushoutShape.wideSpan (Scheme.Γ.obj (op S))
      (fun _ : Fin (n.len + 1) ↦ Scheme.Γ.obj (op Y))
      (fun _ ↦ Scheme.Γ.map f.op) ≅ E :=
    (WidePushoutShape.diagramIsoWideSpan E).symm
  let c := (coconeLeftOpOfCone (Scheme.Γ.rightOp.mapCone (limit.cone D))).whisker
    (widePushoutShapeOp (Fin (n.len + 1)))
  have pc : IsColimit c :=
    (isColimitCoconeLeftOpOfCone (D ⋙ Scheme.Γ.rightOp) P).whiskerEquivalence
      (widePullbackShapeOpEquiv (Fin (n.len + 1))).symm
  exact (IsColimit.precomposeHomEquiv e c).symm pc

/-- 同じ余錐の各環からの脚は、元の広義ファイバー積の射影の Γ。 -/
theorem affineGammaCechCocone_ι (n : SimplexCategory) (i : Fin (n.len + 1)) :
    (affineGammaCechCocone f n).ι.app (some i) =
      Scheme.Γ.map (WidePullback.π (fun _ : Fin (n.len + 1) ↦ f) i).op := rfl

/-- 同じ余錐の基底からの脚も、元の基底への射の Γ。 -/
theorem affineGammaCechCocone_head (n : SimplexCategory) :
    (affineGammaCechCocone f n).ι.app none =
      Scheme.Γ.map (WidePullback.base (fun _ : Fin (n.len + 1) ↦ f)).op := by
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  rfl

end SerrePositivity.AlgebraicGeometry
