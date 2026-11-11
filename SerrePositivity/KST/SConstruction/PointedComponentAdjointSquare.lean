module
public import SerrePositivity.KST.SConstruction.BoundaryAssemblyNaturality

/-! # 同じ点つき随伴比較四角形から suspension 比較四角形へ
概要：随伴構造射の点つき成分での可換性を元の suspension 構造射へ移す。
方針：成分の uncurry と、その両変数の自然性を固定した射で適用する。
規約：Kan 性は不要。使われ方：旧・新 BF 列の全正構造射の比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet Spectra
open Spectra.PointedMapping

/-- 同じ随伴四角形の成分可換性を、元の suspension 四角形へ移す。 -/
lemma pointedComponentAdjointSquare {A B K T : PointedSimplicialSet.{u}}
    (c : A ⟶ K) (d : B ⟶ T) (a : A ⟶ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace B) (σ : _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension K ⟶ T)
    (h : componentOf (c ≫ curry σ) = componentOf
      (a ≫ (PointedObject.basedHomFunctor PointedSimplicialSet.circle.{u}).map d)) :
    componentOf (PointedSimplicialSet.circle.{u} ◁ c ≫ σ) =
      componentOf (uncurry a ≫ d) := by
  have hu := pointedComponentUncurry h
  change componentOf (uncurry (c ≫ curry σ)) =
    componentOf (uncurry (a ≫ (ihom PointedSimplicialSet.circle.{u}).map d)) at hu
  erw [uncurry_natural_left c (curry σ), uncurry_curry,
    uncurry_natural_right a d] at hu
  exact hu

end SerrePositivity.KST.SConstruction
