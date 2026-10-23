module

public import SerrePositivity.InfinityCategories.F1.Coherent.ConstantSourceComparison
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.ConstantDiagramTransportWitness

/-!
概要：定値始域の二種類の直積座標を、全評価の合成で厳密に照合する。
方針：引き戻しの二射影へ移し、元の底と fiber の座標をそれぞれ計算する。
規約：元の底と全高次パラメータを保持する。
使われ方：相対合成の全切断による評価の計算。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 定値全空間の始域座標の逆から fiber を取ると、元の第二射影。 -/
lemma constantSourceOverIso_inv_fiber (B : SSet.{u + 1}) (x : SpaceInfinity.{u} _⦋0⦌) :
    (constantUnstraighteningSourceOverIso B x).inv.left ≫
      F2.constantUnstraighteningFiberProjection B x = snd B (vertexFiber pointedSpaceProjection x) := by
  apply vertexFiber_hom_ext pointedSpaceProjection x
  rw [Category.assoc]
  change _ ≫ (F2.constantPullbackFiberIso pointedSpaceProjection x).hom ≫
    fst _ B ≫ vertexFiberι pointedSpaceProjection x = _
  rw [F2.constantPullbackFiberIso_fst_ι]
  change tensorToPullbackConstant pointedSpaceProjection x B ≫ pullback.fst _ _ = _
  rw [tensorToPullbackConstant, pullback.lift_fst]

/-- 元の定値全空間の fiber 評価を再構成すると、同じ底上の直積射になる。 -/
lemma constantSourceCoordinates {B T : SSet.{u + 1}}
    (x y : SpaceInfinity.{u} _⦋0⦌)
    (f : vertexFiber pointedSpaceProjection x ⊗ T ⟶ vertexFiber pointedSpaceProjection y) :
    (α_ B (vertexFiber pointedSpaceProjection x) T).inv ≫
        ((constantUnstraighteningSourceOverIso B x).inv.left ▷ T) ≫
          lift ((F2.constantUnstraighteningFiberProjection B x ▷ T) ≫ f)
            (fst (leftUnstraightening (SSet.const x : B ⟶ _)) T ≫
              leftUnstraighteningProjection (SSet.const x : B ⟶ _)) ≫
                (F2.constantPullbackFiberIso pointedSpaceProjection y).inv =
      (B ◁ f) ≫ (constantUnstraighteningSourceOverIso B y).inv.left := by
  apply pullback.hom_ext
  · simp only [Category.assoc, F2.constantPullbackFiberIso_inv_fst, lift_fst_assoc]
    change _ = (B ◁ f) ≫ tensorToPullbackConstant pointedSpaceProjection y B ≫ _
    rw [tensorToPullbackConstant, pullback.lift_fst]
    rw [← Category.assoc ((constantUnstraighteningSourceOverIso B x).inv.left ▷ T),
      ← comp_whiskerRight, constantSourceOverIso_inv_fiber]
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    rintro ⟨b, v, t⟩
    rfl
  · simp only [Category.assoc, F2.constantPullbackFiberIso_inv_snd, lift_snd]
    change _ = (B ◁ f) ≫ tensorToPullbackConstant pointedSpaceProjection y B ≫ _
    rw [tensorToPullbackConstant, pullback.lift_snd]
    have hb : (constantUnstraighteningSourceOverIso B x).inv.left ≫
        leftUnstraighteningProjection (SSet.const x : B ⟶ _) =
          fst B (vertexFiber pointedSpaceProjection x) :=
      (constantUnstraighteningSourceOverIso B x).inv.w
    rw [← Category.assoc ((constantUnstraighteningSourceOverIso B x).inv.left ▷ T),
      whiskerRight_fst, Category.assoc, hb]
    rfl

end SerrePositivity.InfinityCategories
