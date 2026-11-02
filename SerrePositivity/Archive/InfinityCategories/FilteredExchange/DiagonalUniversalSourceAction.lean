module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.DiagonalTwoStepUniversalAction

/-!
概要：普遍始点の一段輸送と恒等作用を、元の全区間の始点作用として保持する。
方針：同じ始点と係数の組を、元の輸送と第一射影へ入力する。
規約：全係数を保持。使われ方：定値輸送比較の始点自然性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の全区間の同じ一段始点作用。 -/
def diagonalFiberSourceAction {E B P : SSet.{u}} (p : E ⟶ B) [LeftFibration p]
    {a b : B _⦋0⦌} (c : P ⟶ intervalMappingSpace a b) :
    (ihom P).obj (vertexFiber p a) ⟶ (ihom P).obj (vertexFiber p b) :=
  functorPairRight c ≫ (ihom P).map (parametrizedFiberTransportFamily p a b).endpoint

/-- 普遍始点の一段輸送を関手族上で読むと、元の全区間の始点作用そのもの。 -/
lemma diagonalFiberSourceAction_universal {E B P : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] {a b : B _⦋0⦌} (c : P ⟶ intervalMappingSpace a b) :
    functorPairRight (𝟙 P) ≫ (ihom P).map
      (diagonalFiberTransport p (fst (vertexFiber p a) P) (snd (vertexFiber p a) P ≫ c)) =
        diagonalFiberSourceAction p c := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro f
  apply CategoryTheory.Functor.functorHom_ext
  intro d α
  apply ConcreteCategory.hom_ext
  intro x
  rfl

/-- 始点と元の係数を組にして第一射影で読む作用は、同じ始点関手の恒等作用。 -/
lemma functorPairRight_id_fst {P A : SSet.{u}} :
    functorPairRight (𝟙 P) ≫ (ihom P).map (fst A P) = 𝟙 ((ihom P).obj A) := by
  rw [functorPairRight, ← curry_natural_right, lift_fst, curry_uncurry]

end SerrePositivity.InfinityCategories.F2
