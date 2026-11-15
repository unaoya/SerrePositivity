module

public import SerrePositivity.AlgebraicGeometry.CartesianPullbackComparison
public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal

/-!
概要：Cartesian な比較が誘導する二重交叉の射と、二つの対角の正方形を比較する。
方針：射影での可換式と元の Cartesian 正方形の一意性で対角への lift を作る。
規約：任意の pullback を持つ圏の有限極限の法則。
使われ方：Stacks 01ZQ の分離性の有限段への降下の対角への適用。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory Limits
universe u v
variable {C : Type u} [Category.{v} C] [HasPullbacks C]
  {X Y S T : C} (a : Y ⟶ X) (p : Y ⟶ T) (f : X ⟶ S) (g : T ⟶ S)
  (h : IsPullback a p f g)

/-- Cartesian 比較の二重交叉の射と二つの対角の正方形も Cartesian。 -/
theorem isPullback_diagonal_cartesianPullbackMap :
    IsPullback (pullback.diagonal p) a
      (cartesianPullbackMap p p f f g a a h h) (pullback.diagonal f) := by
  let b := cartesianPullbackMap p p f f g a a h h
  have hfst (s : PullbackCone b (pullback.diagonal f)) :
      s.fst ≫ pullback.fst p p ≫ a = s.snd := by
    simpa [b, cartesianPullbackMap, Category.assoc] using
      congrArg (fun k ↦ k ≫ pullback.fst f f) s.condition
  have hsnd (s : PullbackCone b (pullback.diagonal f)) :
      s.fst ≫ pullback.snd p p ≫ a = s.snd := by
    simpa [b, cartesianPullbackMap, Category.assoc] using
      congrArg (fun k ↦ k ≫ pullback.snd f f) s.condition
  have heq (s : PullbackCone b (pullback.diagonal f)) :
      s.fst ≫ pullback.fst p p = s.fst ≫ pullback.snd p p := by
    apply h.hom_ext
    · simpa only [Category.assoc] using (hfst s).trans (hsnd s).symm
    · simp only [Category.assoc, pullback.condition]
  refine ⟨?_, ⟨PullbackCone.IsLimit.mk _ (fun s ↦ s.fst ≫ pullback.fst p p) ?_ ?_ ?_⟩⟩
  · constructor
    apply pullback.hom_ext <;> simp [cartesianPullbackMap, Category.assoc]
  · intro s
    apply pullback.hom_ext
    · simp
    · simpa only [Category.assoc, pullback.diagonal_snd, Category.comp_id] using heq s
  · intro s
    simpa only [Category.assoc] using hfst s
  · intro s m hm _
    simpa only [Category.assoc, pullback.diagonal_fst, Category.comp_id] using
      congrArg (fun k ↦ k ≫ pullback.fst p p) hm

end SerrePositivity.AlgebraicGeometry
