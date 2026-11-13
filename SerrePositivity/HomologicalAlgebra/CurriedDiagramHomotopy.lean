module
public import SerrePositivity.HomologicalAlgebra.FunctorComplexExchange
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory

/-!
概要：積添字上の鎖ホモトピーを、二重図式の同じ成分へ並べ替える。
方針：次数と二つの添字で評価し、元の自然性・零条件・ホモトピー式を使う。
規約：新しいホモトピーを選ばず、全成分を保持する。
使われ方：HA 1.2.4、IS-W2 A02 の全パラメータ比較への照合。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomologicalComplex
namespace SerrePositivity.HomologicalAlgebra
variable {J K C : Type*} [Category* J] [Category* K] [Category* C] [Preadditive C]
variable {ι : Type*} (c : ComplexShape ι)
local notation "E₁" => functorToComplexOfFunctors (J × K) C c
local notation "E₂" =>
  (Functor.obj (Functor.whiskeringRight J (K ⥤ HomologicalComplex C c)
    (HomologicalComplex (K ⥤ C) c)) (functorToComplexOfFunctors K C c) ⋙
    functorToComplexOfFunctors J (K ⥤ C) c)

/-- 同じ積添字のホモトピーを、二つの添字で評価する形へ戻す。 -/
def curriedDiagramHomotopy {F G : J ⥤ K ⥤ HomologicalComplex C c} (f g : F ⟶ G)
    (h : Homotopy ((E₁).map (Functor.uncurry.map f))
      ((E₁).map (Functor.uncurry.map g))) :
    Homotopy ((E₂).map f) ((E₂).map g) where
  hom i j := {
    app a := {
      app b := (h.hom i j).app (a, b)
      naturality := by
        intro b b' t
        simpa [functorToComplexOfFunctors, Functor.uncurry] using
          (h.hom i j).naturality ((𝟙 a, t) : (a, b) ⟶ (a, b')) }
    naturality := by
      intro a a' t
      apply NatTrans.ext
      funext b
      simpa [functorToComplexOfFunctors, Functor.uncurry] using
        (h.hom i j).naturality ((t, 𝟙 b) : (a, b) ⟶ (a', b)) }
  zero i j hij := by
    apply NatTrans.ext
    funext a
    apply NatTrans.ext
    funext b
    exact NatTrans.congr_app (h.zero i j hij) (a, b)
  comm i := by
    apply NatTrans.ext
    funext a
    apply NatTrans.ext
    funext b
    exact NatTrans.congr_app (h.comm i) (a, b)

end SerrePositivity.HomologicalAlgebra
