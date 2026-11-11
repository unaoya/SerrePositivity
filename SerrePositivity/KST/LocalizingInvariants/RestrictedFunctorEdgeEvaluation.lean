module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomEvaluationNaturality
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.FunctorHoEvaluation

/-!
概要：指定した関手の辺の制限等式を、同じ辺の頂点成分の等式へ移す。
方針：前合成と評価の厳密な可換性を使い、端点の表示は Arrow に含める。
規約：可逆辺を再選択しない。使われ方：d8 の全四角形比較の右辺成分の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

lemma hom_eq_transport_of_arrow_eq {C : Type*} [Category* C] {a b c : C}
    (f : a ⟶ b) (g : c ⟶ b) (ha : a = c) (h : Arrow.mk f = Arrow.mk g) :
    f = eqToHom ha ≫ g := by
  subst c
  simpa using (Arrow.mk_injective a b h)

lemma restrictedFunctorEdge_evaluation_arrow {A B X : SSet.{u}} (i : A ⟶ B)
    {f g : ((ihom B).obj X) _⦋0⦌} {f' g' : ((ihom A).obj X) _⦋0⦌}
    (l : Truncated.Edge (X := (truncation 2).obj ((ihom B).obj X)) f g)
    (m : Truncated.Edge (X := (truncation 2).obj ((ihom A).obj X)) f' g')
    (h : ((pre i).app X).app (Opposite.op ⦋1⦌) l.edge = m.edge) (x : A _⦋0⦌) :
    Arrow.mk ((hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) (i.app (Opposite.op ⦋0⦌) x))).toFunctor.map
      (Truncated.HomotopyCategory.homMk l)) =
    Arrow.mk ((hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) x)).toFunctor.map
      (Truncated.HomotopyCategory.homMk m)) := by
  apply Truncated.HomotopyCategory.congr_arrowMk_homMk
  have he := congrArg (fun k : (ihom B).obj X ⟶ X =>
    k.app (Opposite.op ⦋1⦌) l.edge) (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.evaluateFunctorAt_precomp (X := X) i x)
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) x).app (Opposite.op ⦋1⦌)
    (((pre i).app X).app (Opposite.op ⦋1⦌) l.edge) = _ at he
  rw [h] at he
  exact he.symm

end SerrePositivity.KST.LocalizingInvariants
