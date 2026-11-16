module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.OrdinaryHomTwistedRestrictions

/-!
概要：Hom の twisted arrow 比較の左射影は、指定した反対 nerve の比較を介して元の源射影に一致する。
方針：左の全射列を評価して再反転し、有限順序の二重反転だけを消す。
規約：反対圏と単体集合の反転を定義上同一視しない。
使われ方：Kerodon Proposition 8.1.1.10（Tag 03JN）、HTT 5.1.5.6 の全 Hom 図式の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
variable {C : Type u} [SmallCategory C] {n : ℕ}

private lemma indexMap_heq {A : Type u} [SmallCategory A] (F : Fin (n + 1) ⥤ A)
    {i j i' j' : Fin (n + 1)} (hi : i = i') (hj : j = j')
    (f : i ⟶ j) (g : i' ⟶ j') : HEq (F.map f) (F.map g) := by
  subst i' j'
  have hh : f = g := Subsingleton.elim _ _
  subst g
  rfl

/-- 左の標準単体を評価して反対圏の nerve へ戻すと、元の全射列に戻る。
Kerodon Proposition 8.1.1.10（Tag 03JN）、左添字の模型移送の逆関係。 -/
lemma homChainLeftEvaluation (F : Fin (n + 1) ⥤ Cᵒᵖ) :
    nerveReverseChain (SSet.yonedaEquiv ((stdSimplex.opIso ⦋n⦌).inv ≫
      homChainLeftWeight.{u} n ≫
        nerveMap ((homChainIndexDown n).op ⋙ F.leftOp))) = F := by
  refine CategoryTheory.Functor.hext ?_ ?_
  · intro i
    change F.obj i.rev.rev.rev.rev = F.obj i
    simp only [Fin.rev_rev]
  · intro i j h
    change HEq (F.map (homOfLE _)) (F.map h)
    apply indexMap_heq F
    · change i.rev.rev.rev.rev = i
      simp only [Fin.rev_rev]
    · change j.rev.rev.rev.rev = j
      simp only [Fin.rev_rev]

/-- 左射影は指定した反対 nerve の比較を介して、元の Hom の源射影と厳密に一致する。
Kerodon Proposition 8.1.1.10（Tag 03JN）、同じ両端射影を保つ比較の左側。 -/
lemma ordinaryHomTwistedComparison_left :
    ordinaryHomTwistedComparison C ≫ edgewiseLeft (nerve C) ≫ nerveOppositeMap =
      nerveMap (ordinaryHomElementsProjection C ⋙ CategoryTheory.Prod.fst Cᵒᵖ C) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  change nerveReverseChain (SSet.yonedaEquiv ((stdSimplex.opIso n.unop).inv ≫
    (joinInl _ _ ≫ ordinaryHomTwistedSimplex s))) = _
  rw [ordinaryHomTwistedSimplex_inl]
  exact homChainLeftEvaluation
    (s ⋙ ordinaryHomElementsProjection C ⋙ CategoryTheory.Prod.fst Cᵒᵖ C)

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
