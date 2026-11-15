module

public import SerrePositivity.AlgebraicGeometry.CartesianClosedImmersionLimit
public import SerrePositivity.AlgebraicGeometry.FlatStageModelLimit

/-!
概要：二段の実際の底変換の模型の射の閉埋め込み性を、極限から有限段へ降ろす。
方針：元の頂点を保つ既存の極限と Cartesian 正方形に C04 の移送を適用する。
規約：模型の存在・Noether 性・忠実平坦な遷移は追加仮定にしない。
使われ方：対角の模型を通じた分離性の有限段への降下。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u

/-- 二段の底変換の極限射の閉埋め込み性は、実際の模型の射のある後段へ降りる。 -/
theorem exists_closedImmersion_flatStageProjection_of_isLimit
    {J : Type u} [SmallCategory J] [IsCofiltered J]
    (D : J ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {j k} (f : j ⟶ k), IsAffineHom (D.map f)]
    [∀ j, CompactSpace (D.obj j)] [∀ j, QuasiSeparatedSpace (D.obj j)]
    (i : J) {X T Y Z : Scheme.{u}}
    (a : X ⟶ T) (x : X ⟶ c.pt) (r : T ⟶ D.obj i)
    [QuasiCompact r] [QuasiSeparated r]
    (hpb : IsPullback a x r (c.π.app i)) (β : T ⟶ Y) (q : Z ⟶ Y)
    [QuasiCompact q] [QuasiSeparated q] [LocallyOfFiniteType q]
    [IsClosedImmersion (pullback.snd q (a ≫ β))] :
    ∃ j : Over i, IsClosedImmersion ((flatStageModelProjection D i r β q).app j) := by
  let B := stageBaseChangeDiagram D i r
  let E := flatStageModelDiagram D i r β q
  let cb := stageModelCone D c i a x r hpb
  let ce := flatStageModelConeWithPoint D c i a x r hpb β q (a ≫ β) rfl
  let τ := flatStageModelProjection D i r β q
  haveI (j : Over i) : CompactSpace (B.obj j) := by dsimp [B]; infer_instance
  haveI (j : Over i) : QuasiSeparatedSpace (B.obj j) := by dsimp [B]; infer_instance
  haveI {j k : Over i} (f : j ⟶ k) : IsAffineHom (B.map f) := by dsimp [B]; infer_instance
  let o : Over i := Over.mk (𝟙 i)
  haveI : QuasiCompact (τ.app o) := by dsimp [τ, flatStageModelProjection]; infer_instance
  haveI : QuasiSeparated (τ.app o) := by dsimp [τ, flatStageModelProjection]; infer_instance
  haveI : LocallyOfFiniteType (τ.app o) := by dsimp [τ, flatStageModelProjection]; infer_instance
  obtain ⟨j, _, hj⟩ := exists_closedImmersion_stage_of_cartesian_limit B E τ cb
    (isLimit_stageModelCone D c hc i a x r hpb) o
    (pullback.snd q (a ≫ β)) (ce.π.app o)
    (isPullback_flatStageModelConeWithPoint_π D c i a x r hpb β q (a ≫ β) rfl o)
    (fun j f ↦ isPullback_flatStageModelDiagram_map D i r β q f)
  exact ⟨j, hj⟩

end SerrePositivity.AlgebraicGeometry
