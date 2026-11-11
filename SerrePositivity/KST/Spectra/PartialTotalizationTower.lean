module

public import SerrePositivity.KST.Spectra.PartialTotalizationKan
public import SerrePositivity.KST.Spectra.SkeletalTransitionReedyMono
public import SerrePositivity.KST.Spectra.PointedReedyWeightRestriction
public import SerrePositivity.KST.Spectra.PointedTotalizationEndIso

/-!
概要：通常 Tot の有限骨格による実際の点つき Kan fibration の塔。
方針：骨格の Reedy cofibrancy と包含の Reedy 単射性を、end の Kan 性・制限の fibration 性へ渡す。
規約：塔は既存の SkeletalWeightedEnd の対象と射そのもの。
使われ方：Goerss–Jardine VIII §1。通常 Tot の Milnor 比較の塔。
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits SSet Opposite HomotopicalAlgebra
open SSet.modelCategoryQuillen
open SerrePositivity.Reedy
namespace SerrePositivity.KST.Spectra.PartialTotalizationTower
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

abbrev diagram (X : CosimplicialObject PointedSimplicialSet.{u}) :
    ℕᵒᵖ ⥤ PointedSimplicialSet.{u} :=
  SkeletalWeightedEnd.tower (AsSmall.down ⋙ stdSimplex) (AsSmall.down ⋙ X)

abbrev stage (X : CosimplicialObject PointedSimplicialSet.{u}) (n : ℕ) :=
  (diagram X).obj (op n)

abbrev step (X : CosimplicialObject PointedSimplicialSet.{u}) (n : ℕ) :
    stage X (n + 1) ⟶ stage X n :=
  (diagram X).map (homOfLE (Nat.le_succ n)).op

/-- 各段は元の係数の Reedy 条件から Kan。 -/
lemma stage_kanComplex (X : CosimplicialObject PointedSimplicialSet.{u})
    (hX : reedyRight simplex J.rlp (terminal.from (X ⋙ PointedSimplicialSet.forget))) (n : ℕ) :
    KanComplex (stage X n).right := PointedTotalization.partialEnd_kanComplex X hX n

/-- 骨格への全ての制限は実際の Kan fibration。 -/
lemma map_fibration (X : CosimplicialObject PointedSimplicialSet.{u})
    (hX : reedyRight simplex J.rlp (terminal.from (X ⋙ PointedSimplicialSet.forget)))
    {n m : ℕ} (h : n ≤ m) : Fibration ((diagram X).map (homOfLE h).op).right := by
  exact PointedWeightedEnd.preMap_fibration
    (SkeletalStandardLatching.transition.{u} (Nat.add_le_add_right h 1))
    (SkeletalStandardLatching.transition_reedy_mono (Nat.add_le_add_right h 1)) X hX

/-- 通常 Tot から骨格の段への元の制限射。 -/
def restriction (X : CosimplicialObject PointedSimplicialSet.{u}) (n : ℕ) :
    PointedTotalization.obj X ⟶ stage X n :=
  (PointedTotalization.standardEndIso X).hom ≫
    (SkeletalWeightedEnd.cone (AsSmall.down ⋙ stdSimplex) (AsSmall.down ⋙ X)).π.app (op n)

end
end SerrePositivity.KST.Spectra.PartialTotalizationTower
