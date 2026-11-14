module
public import SerrePositivity.HomotopicalAlgebra.Diagram.FrameWeightFunctoriality

/-!
概要：元の重み付き実現随伴の単位の係数frameに関する自然性。
方針：同じmateのHom同値の自然性を恒等射で評価する。
規約：既存構成の単位則。重み・frame・実現関手を変更しない。
使われ方：BE Totの普遍重み付き錐の全図式射に対する照合。
-/
@[expose] public noncomputable section
universe w u
open CategoryTheory CategoryTheory.Limits
namespace SerrePositivity.DiagramModel.FrameWeightRealization
variable (K : Type w) [SmallCategory K] {C : Type u} [Category.{w} C]
  [HasColimitsOfSize.{w,w} C]

/-- 同じ随伴単位と係数frameのmateは、全重みの自然変換として可換。 -/
theorem unit_frame_naturality {B B' : K ⥤ SimplexCategory ⥤ C}
    (a : B ⟶ B') (W : Kᵒᵖ ⥤ SSet.{w}) :
    (adjunction K B').unit.app W ≫ ((homFamily K).map a.op).app ((functor K B').obj W) =
      (adjunction K B).unit.app W ≫ (hom K B).map ((map K a).app W) := by
  unfold map
  exact unit_conjugateEquiv_symm (adjunction K B') (adjunction K B)
    ((homFamily K).map a.op) W

end SerrePositivity.DiagramModel.FrameWeightRealization
