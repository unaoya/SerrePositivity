module

public import SerrePositivity.AlgebraicGeometry.FrobeniusArrowNaturality

/-!
概要：実際の Frobenius の矢印の増大 conerve の、同じ余極限への自然な比較。
方針：既存の増大 conerve 関手を、検証した矢印の標準比較と自然性に適用する。
規約：増大項と全ての次数の射を同時に保つ。
使われ方：同じアフィン Čech 複体と Frobenius 係数の自然性。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
universe u

/-- 実際の Frobenius 順極限の矢印と、同じ図式の余極限の増大 conerve の標準同型。 -/
def frobeniusAugmentedConerveColimitIso (f : Arrow CommRingCat.{u})
    (p : ℕ) (hp : p.Prime) (hA : (p : f.left) = 0) (hB : (p : f.right) = 0) :
    (Arrow.mk (CommRingCat.ofHom
      (frobeniusDirectLimitMap p hp hA hB f.hom.hom))).augmentedCechConerve ≅
      (colimit (frobeniusArrowSmallDiagram f p hp hA hB)).augmentedCechConerve :=
  CosimplicialObject.augmentedCechConerve.mapIso
    (frobeniusArrowSmallColimitIso f p hp hA hB)

/-- 標準比較は元の可換な四角形の増大 conerve の射に自然。
増大項と正次数の全ての写像を、同じ既存の関手で保つ。 -/
theorem frobeniusAugmentedConerveColimitIso_naturality
    {f g : Arrow CommRingCat.{u}} (F : f ⟶ g) (p : ℕ) (hp : p.Prime)
    (hA : (p : f.left) = 0) (hB : (p : f.right) = 0)
    (hC : (p : g.left) = 0) (hD : (p : g.right) = 0) :
    Arrow.mapAugmentedCechConerve (frobeniusDirectLimitArrowMap F p hp hA hB hC hD) ≫
        (frobeniusAugmentedConerveColimitIso g p hp hC hD).hom =
      (frobeniusAugmentedConerveColimitIso f p hp hA hB).hom ≫
        Arrow.mapAugmentedCechConerve
          (colim.map (frobeniusArrowSmallDiagramMap F p hp hA hB hC hD)) := by
  let G : Arrow CommRingCat.{u} ⥤ CosimplicialObject.Augmented CommRingCat.{u} :=
    CosimplicialObject.augmentedCechConerve
  exact (G.map_comp _ _).symm.trans
    ((congrArg G.map (frobeniusArrowSmallColimitIso_naturality F p hp hA hB hC hD)).trans
      (G.map_comp _ _))

end SerrePositivity.AlgebraicGeometry
