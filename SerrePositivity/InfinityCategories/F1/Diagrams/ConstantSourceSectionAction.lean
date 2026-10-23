module

public import SerrePositivity.InfinityCategories.F1.Diagrams.ConstantSourceSectionMap
public import SerrePositivity.InfinityCategories.F1.Diagrams.ConstantSourceCoordinates
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.ConstantUnstraighteningCoordinates

/-!
概要：定値 fiber 間の全写像の族の底上の後合成を、全切断への同じ後合成へ移す。
方針：定値標的比較を戻し、相対評価を直積座標で再構成して全切断で評価する。
規約：元の底上の射と全高次パラメータを保持する。
使われ方：定値図式の輸送比較を元の錐の全 Hom 比較へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
variable {B T : SSet.{u + 1}} (F : B ⟶ SpaceInfinity.{u})
  (x y : SpaceInfinity.{u} _⦋0⦌)
  (g : leftUnstraightening (SSet.const y : B ⟶ _) ⟶ leftUnstraightening F)
  (hg : g ≫ leftUnstraighteningProjection F =
    leftUnstraighteningProjection (SSet.const y : B ⟶ _))

/-- 元の fiber 間の全関手を底上の射として後合成し全切断へ戻すと、同じ全切断射への後合成。 -/
lemma constantSourceSectionMap_action
    (s : T ⟶ (ihom (vertexFiber pointedSpaceProjection x)).obj
      (vertexFiber pointedSpaceProjection y)) :
    (((s ≫ (pre (F2.constantUnstraighteningFiberProjection B x)).app
          (vertexFiber pointedSpaceProjection y)) ≫
        (F2.constantUnstraighteningRelativeIso
          (leftUnstraighteningProjection (SSet.const x : B ⟶ _)) y).inv) ≫
      HomotopyLimits.relativeFunctorPost (leftUnstraighteningProjection (SSet.const y : B ⟶ _))
        (leftUnstraighteningProjection F) g hg
        (leftUnstraighteningProjection (SSet.const x : B ⟶ _))) ≫
      (constantUnstraighteningSourceRelativeIso F x).hom =
    s ≫ (ihom (vertexFiber pointedSpaceProjection x)).map (constantSourceSectionMap F y g hg) := by
  apply uncurry_injective
  apply HomotopyLimits.simplicialSections_hom_ext
  rw [constantUnstraighteningSourceRelativeIso_evaluation, relativeFunctorPost_uncurry,
    uncurry_natural_right, whiskerLeft_comp]
  simp only [Category.assoc]
  rw [constantSourceSectionMap_evaluation]
  have hc := F2.constantUnstraighteningRelativeIso_reconstruct
    (leftUnstraighteningProjection (SSet.const x : B ⟶ _)) y
    ((s ≫ (pre (F2.constantUnstraighteningFiberProjection B x)).app
      (vertexFiber pointedSpaceProjection y)) ≫
        (F2.constantUnstraighteningRelativeIso
          (leftUnstraighteningProjection (SSet.const x : B ⟶ _)) y).inv)
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at hc
  rw [uncurry_pre_app] at hc
  rw [hc]
  simpa only [Category.assoc] using congrArg (fun q ↦ q ≫ g)
    (constantSourceCoordinates (B := B) x y (uncurry s))

end SerrePositivity.InfinityCategories
