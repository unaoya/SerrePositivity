module

public import SerrePositivity.InfinityCategories.F1.Diagrams.ConstantSourceSectionAction
public import SerrePositivity.InfinityCategories.F2.ConstantDiagramTransportComparison
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FunctorSpaceCurrying

/-!
概要：定値図式の元の輸送作用と底上の射の合成を、全切断写像への同じ後合成と比較する。
方針：定値図式の指定輸送同型を curry し、保持した底上の射で後合成する。
規約：元の輸送族・底上の射・全パラメータを保持する。
使われ方：native な錐の全 Hom 比較の同値性を結論する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- 同じ定値変換の相対像の後合成は、元の普遍輸送と全切断写像の合成と同型。 -/
def constantDiagramSectionTransportIso {B T : SSet.{u + 1}} (F : B ⟶ SpaceInfinity.{u})
    {x y : SpaceInfinity.{u} _⦋0⦌}
    (g : leftUnstraightening (SSet.const y : B ⟶ _) ⟶ leftUnstraightening F)
    (hg : g ≫ leftUnstraighteningProjection F =
      leftUnstraighteningProjection (SSet.const y : B ⟶ _))
    (a : T ⟶ intervalMappingSpace x y) :
    FunctorIso (((F2.constantDiagramTransformation B a ≫
        leftUnstraighteningMappingSpaceMap (SSet.const x : B ⟶ _) (SSet.const y)) ≫
      HomotopyLimits.relativeFunctorPost (leftUnstraighteningProjection (SSet.const y : B ⟶ _))
        (leftUnstraighteningProjection F) g hg
        (leftUnstraighteningProjection (SSet.const x : B ⟶ _))) ≫
          (constantUnstraighteningSourceRelativeIso F x).hom)
      ((F2.pointedIntervalTransport a).map ≫
        (ihom (vertexFiber pointedSpaceProjection x)).map (constantSourceSectionMap F y g hg)) := by
  have e := (F2.constantDiagramMappingTransportIso B a).curry
  rw [curry_uncurry] at e
  have hc : curry ((F2.constantUnstraighteningFiberProjection B x ▷ T) ≫
      (F2.pointedIntervalTransport a).endpoint) =
      (F2.pointedIntervalTransport a).map ≫
        (pre (F2.constantUnstraighteningFiberProjection B x)).app
          (vertexFiber pointedSpaceProjection y) := by
    apply uncurry_injective
    rw [uncurry_curry, uncurry_pre_app]
    change _ = (F2.constantUnstraighteningFiberProjection B x ▷ T) ≫
      uncurry (curry (F2.pointedIntervalTransport a).endpoint)
    rw [uncurry_curry]
  rw [hc] at e
  have E := e.postcomp ((F2.constantUnstraighteningRelativeIso
      (leftUnstraighteningProjection (SSet.const x : B ⟶ _)) y).inv ≫
    HomotopyLimits.relativeFunctorPost (leftUnstraighteningProjection (SSet.const y : B ⟶ _))
      (leftUnstraighteningProjection F) g hg
      (leftUnstraighteningProjection (SSet.const x : B ⟶ _)) ≫
        (constantUnstraighteningSourceRelativeIso F x).hom)
  simp only [Category.assoc, Iso.hom_inv_id_assoc] at E
  have ha := constantSourceSectionMap_action F x y g hg (F2.pointedIntervalTransport a).map
  simp only [Category.assoc] at ha
  rw [ha] at E
  exact E

end SerrePositivity.InfinityCategories
