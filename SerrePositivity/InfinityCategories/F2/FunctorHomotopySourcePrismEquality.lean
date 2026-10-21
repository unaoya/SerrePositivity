module

public import SerrePositivity.InfinityCategories.F2.FunctorHomotopySourceComparison

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

/-- 同じ実延長と同じ終点の底を持つ証拠の実終点は、二射影を含めて厳密に一致する。 -/
lemma RelativeExtensionEndpointWitness.endpoint_eq_of_extension
    {A D C E Q B : SSet.{u}} {q : E ⟶ B} {b : A ⟶ B} {i : D ⟶ A} {v : D ⟶ E}
    {j : C ⟶ A} {f : Q ⟶ B} {a : C ⟶ Q}
    (w w' : RelativeExtensionEndpointWitness q b i v j f a)
    (he : w.extension = w'.extension) : w.endpoint = w'.endpoint := by
  apply pullback.hom_ext
  · exact w.evaluate.symm.trans ((congrArg (fun e => j ≫ e) he).trans w'.evaluate)
  · exact w.endpoint_over.trans w'.endpoint_over.symm

/-- 全底と初期値を保つ二面の共有辺の実 prism が同じなら、元の指定比較も同じ値。 -/
lemma functorHomotopySourceEndpointIso_heq_of_prism
    {B C : SSet.{u + 1}} {F G : B ⟶ SpaceInfinity.{u}}
    (H : SSet.Homotopy F G) (p : C ⟶ B) (s t : C ⟶ leftUnstraightening F)
    (hs : s ≫ leftUnstraighteningProjection F = p)
    (ht : t ≫ leftUnstraighteningProjection F = p)
    (w : RelativeExtensionEndpointWitness pointedSpaceProjection
      ((Δ[1] ◁ p) ≫ functorSimplexDiagram (curry H.h)) (prismEndpoint 0 C)
      (s ≫ pullback.fst pointedSpaceProjection F) (prismEndpoint 1 C) G p)
    (w' : RelativeExtensionEndpointWitness pointedSpaceProjection
      ((Δ[1] ◁ p) ≫ functorSimplexDiagram (curry H.h)) (prismEndpoint 0 C)
      (t ≫ pullback.fst pointedSpaceProjection F) (prismEndpoint 1 C) G p)
    (h : s = t) (he : w.extension = w'.extension) :
    HEq (functorHomotopySourceEndpointIso H p s hs w)
      (functorHomotopySourceEndpointIso H p t ht w') := by
  subst t
  have hw := w.eq_of_extension_endpoint w' he (w.endpoint_eq_of_extension w' he)
  subst w'
  rfl

end SerrePositivity.InfinityCategories.F2
