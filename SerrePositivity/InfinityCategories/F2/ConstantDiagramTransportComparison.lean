module

public import SerrePositivity.InfinityCategories.F2.ConstantDiagramTransportWitness
public import SerrePositivity.InfinityCategories.F2.ConstantUnstraighteningEvaluation
public import SerrePositivity.InfinityCategories.F2.PointedIntervalTransport
public import SerrePositivity.InfinityCategories.F1.UnstraighteningFamilyWitnessRestriction

/-!
概要：定値図式間の実際の unstraightening 比較の fiber 評価を普遍 pointed-space 輸送と比較する。
方針：元の比較の普遍証拠を制限し、同じ底の区間と始点を持つ輸送の一意性を使う。
規約：全パラメータの関手同型として保持する。
使われ方：元の余錐の全 Hom 比較から、底に依存しない fiber 作用への移送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：定値図式の実際の比較の像を表す元の pointed な証拠。
方針：普遍証拠を指定した全区間の族で制限する。
規約：元の比較の像を保つ。使われ方：実際の作用の輸送としての表示。 -/
def constantDiagramMappingFamilyWitness {T : SSet.{u + 1}}
    (B : SSet.{u + 1}) {x y : SpaceInfinity.{u} _⦋0⦌}
    (a : T ⟶ intervalMappingSpace x y) :
    UnstraighteningFamilyWitness (SSet.const x : B ⟶ _) (SSet.const y)
      (constantDiagramTransformation B a)
      (relativeFunctorUncurry (constantDiagramTransformation B a ≫
        leftUnstraighteningMappingSpaceMap (SSet.const x : B ⟶ _) (SSet.const y))) := by
  simpa only [Category.comp_id, relativeFunctorUncurry_naturality] using
    (unstraighteningUniversalFamilyWitness (SSet.const x : B ⟶ _) (SSet.const y)).comp
      (constantDiagramTransformation B a)

/-- 概要：元の定値図式の比較の fiber 評価は、元の区間の普遍輸送の係数制限と同型。
方針：元の証拠を輸送族へ読み替え、全族での輸送の選択独立性を使う。
規約：任意の底と全高次パラメータ。使われ方：全 Hom の定値 fiber の作用。 -/
def constantDiagramMappingTransportIso {T : SSet.{u + 1}}
    (B : SSet.{u + 1}) {x y : SpaceInfinity.{u} _⦋0⦌}
    (a : T ⟶ intervalMappingSpace x y) :
    FunctorIso
      (uncurry ((constantDiagramTransformation B a ≫
        leftUnstraighteningMappingSpaceMap (SSet.const x : B ⟶ _) (SSet.const y)) ≫
          (constantUnstraighteningRelativeIso
            (leftUnstraighteningProjection (SSet.const x : B ⟶ _)) y).hom))
      ((constantUnstraighteningFiberProjection B x ▷ T) ≫
        (pointedIntervalTransport a).endpoint) := by
  let w := constantDiagramTransportWitness (constantDiagramMappingFamilyWitness B a)
  have hw : uncurry ((constantDiagramTransformation B a ≫
      leftUnstraighteningMappingSpaceMap (SSet.const x : B ⟶ _) (SSet.const y)) ≫
        (constantUnstraighteningRelativeIso
          (leftUnstraighteningProjection (SSet.const x : B ⟶ _)) y).hom) = w.endpoint := by
    apply vertexFiber_hom_ext pointedSpaceProjection y
    rw [constantUnstraighteningRelativeIso_uncurry]
    dsimp only [w, constantDiagramTransportWitness]
    rw [vertexFiberLift_ι]
  have e := pointedIntervalTransportComparison (constantUnstraighteningFiberProjection B x) a w
  rw [← hw] at e
  exact e

end SerrePositivity.InfinityCategories.F2
