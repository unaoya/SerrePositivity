module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.ArrowEndpointPair
/-!
概要：全 path の引き戻しの二端点を、同じ二入力の指定像として回収する。
方針：引き戻しの可換式を二つの直積射影へ送る。
規約：射の等式を保持する。使われ方：元入力付き対角 path の端点照合。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
variable {A B Z : SSet.{u}} (f : A ⟶ Z) (g : B ⟶ Z)

lemma dgGluingPathPullback_start :
    pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.arrowEndpointPair Z) (f ⊗ₘ g) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
    pullback.snd (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.arrowEndpointPair Z) (f ⊗ₘ g) ≫ fst A B ≫ f := by
  have h := congrArg (fun k => k ≫ fst Z Z)
    (pullback.condition (f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.arrowEndpointPair Z) (g := f ⊗ₘ g))
  simpa only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.arrowEndpointPair, lift_fst, tensorHom_fst] using h

lemma dgGluingPathPullback_end :
    pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.arrowEndpointPair Z) (f ⊗ₘ g) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
    pullback.snd (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.arrowEndpointPair Z) (f ⊗ₘ g) ≫ snd A B ≫ g := by
  have h := congrArg (fun k => k ≫ snd Z Z)
    (pullback.condition (f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.arrowEndpointPair Z) (g := f ⊗ₘ g))
  simpa only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.arrowEndpointPair, lift_snd, tensorHom_snd] using h

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
