module
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic


/-!
分割で生成：docstring を書き直すこと
概要：filtered な底上の fiber ごとの積の全空間から、全空間の積への射は right cofinal。
方針：元の二項対角の、二つの left fibration の直積に沿う引き戻しとして表示する。
規約：元の二射影そのものの組を比較射に取る。
使われ方：積の全空間 Kan 比較の弱同値性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 概要：fiber ごとの積は、直積の底射に沿う底の対角の引き戻し。
方針：引き戻しへの射を二成分から構成し、底の一致を対角の両射影で読む。
規約：底も全空間も任意。使われ方：元の全空間比較への cofinality の輸送。 -/
lemma fiberProduct_binaryDiagonal_isPullback {E D B : SSet.{u}}
    (p : E ⟶ B) (q : D ⟶ B) :
    IsPullback (lift (pullback.fst p q) (pullback.snd p q))
      (pullback.fst p q ≫ p) (p ⊗ₘ q) (lift (𝟙 B) (𝟙 B)) := by
  have hc : lift (pullback.fst p q) (pullback.snd p q) ≫ (p ⊗ₘ q) =
      (pullback.fst p q ≫ p) ≫ lift (𝟙 B) (𝟙 B) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, tensorHom_fst, lift_fst_assoc, lift_fst, Category.comp_id]
    · simp only [Category.assoc, tensorHom_snd, lift_snd_assoc, lift_snd, Category.comp_id]
      exact pullback.condition.symm
  apply IsPullback.of_isLimit (c := PullbackCone.mk _ _ hc)
  apply PullbackCone.isLimitAux'
  intro s
  have h₀ : (s.fst ≫ fst E D) ≫ p = s.snd := by
    have h := congrArg (fun r ↦ r ≫ fst B B) s.condition
    simpa only [Category.assoc, tensorHom_fst, lift_fst, Category.comp_id] using h
  have h₁ : (s.fst ≫ snd E D) ≫ q = s.snd := by
    have h := congrArg (fun r ↦ r ≫ snd B B) s.condition
    simpa only [Category.assoc, tensorHom_snd, lift_snd, Category.comp_id] using h
  let a := pullback.lift (s.fst ≫ fst E D) (s.fst ≫ snd E D) (h₀.trans h₁.symm)
  refine ⟨a, ?_, ?_, ?_⟩
  · change a ≫ lift (pullback.fst p q) (pullback.snd p q) = s.fst
    apply CartesianMonoidalCategory.hom_ext
    · simp only [a, Category.assoc, lift_fst, pullback.lift_fst]
    · simp only [a, Category.assoc, lift_snd, pullback.lift_snd]
  · change a ≫ (pullback.fst p q ≫ p) = s.snd
    dsimp only [a]
    rw [← Category.assoc, pullback.lift_fst]
    exact h₀
  · intro m hm _
    change m ≫ lift (pullback.fst p q) (pullback.snd p q) = s.fst at hm
    apply pullback.hom_ext (f := p) (g := q)
    · have h := congrArg (fun r ↦ r ≫ fst E D) hm
      simpa only [a, Category.assoc, lift_fst, pullback.lift_fst] using h
    · have h := congrArg (fun r ↦ r ≫ snd E D) hm
      simpa only [a, Category.assoc, lift_snd, pullback.lift_snd] using h

end SerrePositivity.InfinityCategories.Project.FilteredExchange
