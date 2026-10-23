module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorHomotopySourcePrismEquality

/-!
概要：二面の共有辺の同じ実 prism は、同じ元の指定始域比較を値まで保持する。
方針：元の実終点を二射影で回収し、初期値の表示変更を消去する。
規約：比較を選び直さない。使われ方：全三単体の四面で共有する辺の比較の同定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

variable {B C : SSet.{u + 1}} {F G : B ⟶ SpaceInfinity.{u}}
  (H : SSet.Homotopy F G) (p : C ⟶ B) (s t : C ⟶ leftUnstraightening F)
  (hs : s ≫ leftUnstraighteningProjection F = p)
  (ht : t ≫ leftUnstraighteningProjection F = p)
  (w : RelativeExtensionEndpointWitness pointedSpaceProjection
    ((Δ[1] ◁ p) ≫ functorSimplexDiagram (curry H.h)) (prismEndpoint 0 C)
    (s ≫ pullback.fst pointedSpaceProjection F) (prismEndpoint 1 C) G p)
  (w' : RelativeExtensionEndpointWitness pointedSpaceProjection
    ((Δ[1] ◁ p) ≫ functorSimplexDiagram (curry H.h)) (prismEndpoint 0 C)
    (t ≫ pullback.fst pointedSpaceProjection F) (prismEndpoint 1 C) G p)
  (he : w.extension = w'.extension)

include hs ht w w' he

/-- 同じ全底と同じ実 prism は、両面の実始点も二射影を含めて厳密に回収する。 -/
lemma functorHomotopySource_eq_of_prism : s = t := by
  apply pullback.hom_ext
  · exact w.initial.symm.trans
      ((congrArg (fun e => prismEndpoint 0 C ≫ e) he).trans w'.initial)
  · exact hs.trans ht.symm

/-- 二面で共有する同じ実 prism と底だけから、元の指定始域比較の値を同定できる。 -/
lemma functorHomotopySourceEndpointIso_heq_shared_prism :
    HEq (functorHomotopySourceEndpointIso H p s hs w)
      (functorHomotopySourceEndpointIso H p t ht w') :=
  functorHomotopySourceEndpointIso_heq_of_prism H p s t hs ht w w'
    (functorHomotopySource_eq_of_prism H p s t hs ht w w' he) he

end SerrePositivity.InfinityCategories.F2
