module

public import SerrePositivity.EInfinity.BarrattEccles.MappingSpaceHammockPrecompose
public import SerrePositivity.EInfinity.BarrattEccles.MappingSpaceHammockPostcompose

/-!
# 既存 Map^h と reduced hammock の比較の全両端点自然性

概要：元の両端点の二つの射を同時に動かす比較の正方形を得る。
方針：元の始域・終域作用の二つの自然性を合成する。
規約：元の全単体・既存比較・任意の両端点射を保持する。
使われ方：実 DK Hom と元の Map^h の全自然比較。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Opposite SerrePositivity.SimplicialModel
variable (A : Type u) [CommRing A]

lemma mappingSpaceReducedHammockComparisonIso_naturality
    {X' X Y Y' : (operad A).Algebra} (f : X' ⟶ X) (g : Y ⟶ Y') :
    AnodyneHomotopy.anodyneQ.map (SSet.uliftFunctor.{u + 1, u}.map
        ((((mappingSpace A).map f.op).app Y) ≫ (((mappingSpace A).obj (op X')).map g))) ≫
      (mappingSpaceReducedHammockComparisonIso A X' Y').hom =
    (mappingSpaceReducedHammockComparisonIso A X Y).hom ≫
      AnodyneHomotopy.anodyneQ.map
        (algebraReducedHammockPrecompose A Y f ≫ algebraReducedHammockPostcompose A X' g) := by
  simp only [Functor.map_comp]
  rw [Category.assoc, mappingSpaceReducedHammockComparisonIso_postcompose,
    ← Category.assoc, mappingSpaceReducedHammockComparisonIso_precompose, Category.assoc]

end SerrePositivity.EInfinity.BarrattEccles
