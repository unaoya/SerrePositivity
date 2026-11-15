module

public import SerrePositivity.AlgebraicGeometry.FlatStageModelProperties
public import SerrePositivity.AlgebraicGeometry.CartesianFlatModelSurjectivity

/-!
概要：実際の平坦模型の図式の成分を、ある有限段で全射にする。
方針：元の被覆を頂点に保つ cone の Cartesian 性を、成分の全射性の比較へ渡す。
規約：同じ実際の模型の法則。r の準コンパクト性以外に固有性は使わない。
使われ方：A07 の平坦側の全射性を同じ有限段へ移す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u

/-- 元の平坦被覆が全射なら、ある有限段の実際の被覆射も全射。 -/
theorem exists_surjective_flat_stage_of_model
    {J : Type u} [SmallCategory J] [IsCofiltered J]
    (D : J ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ i, CompactSpace (D.obj i)]
    (i : J) {X T Y Z : Scheme.{u}} (a : X ⟶ T) (x : X ⟶ c.pt) (r : T ⟶ D.obj i)
    (hpb : IsPullback a x r (c.π.app i)) [QuasiCompact r]
    (β : T ⟶ Y) (q : Z ⟶ Y) [Flat q] [LocallyOfFinitePresentation q] [QuasiCompact q]
    (b : X ⟶ Y) (hb : a ≫ β = b) [Surjective (pullback.snd q b)] :
    ∃ j : Over i, Surjective ((flatStageModelProjection D i r β q).app j) :=
  exists_surjective_component_of_cartesian_flat_model (stageBaseChangeDiagram D i r)
    (stageModelCone D c i a x r hpb) (isLimit_stageModelCone D c hc i a x r hpb)
    (flatStageModelDiagram D i r β q) (flatStageModelProjection D i r β q)
    (fun f ↦ isPullback_flatStageModelDiagram_map D i r β q f)
    (pullback.snd q b)
    (fun j ↦ (flatStageModelConeWithPoint D c i a x r hpb β q b hb).π.app j)
    (fun j ↦ isPullback_flatStageModelConeWithPoint_π D c i a x r hpb β q b hb j)

end SerrePositivity.AlgebraicGeometry
