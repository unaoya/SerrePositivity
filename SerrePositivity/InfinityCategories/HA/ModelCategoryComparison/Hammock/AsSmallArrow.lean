module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.AsSmallComparison
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColimitArrowMap

/-!
概要：同じ宇宙比較は元の通常射の hammock 点を厳密に保持する。
方針：元の forward 語の標準射との可換性を一定単体で評価する。
規約：元の相対構造・元の射を保持する。
使われ方：全 right frame 比較の零単体の宇宙回収。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.AsSmallComparison
open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.IsMultiplicative]
  {X Y : C}

/-- 概要：同じ AsSmall 比較は元の射の全一定単体を元の持ち上げた射へ送る。
方針：同じ forward 語の標準射の可換性を各単体で使う。
規約：実射の等式。使われ方：元の局所化射の零単体回収。 -/
lemma arrowMap_colimitIso (f : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap W f ≫ (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.AsSmallComparison.colimitIso W X Y).hom = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.AsSmallComparison.weak W) (AsSmall.up.map f) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro x
  cases x
  have h := congrArg (fun a => a.app n (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowSimplex W f n))
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.AsSmallComparison.graphInclusion_colimitIso W X Y (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward))
  refine h.trans ?_
  apply congrArg ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.AsSmallComparison.weak W) (AsSmall.up.obj X) (AsSmall.up.obj Y)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward)).app n)
  let F := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowSimplex W f n ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.functor (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.AsSmallComparison.up W)
  let G := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowSimplex (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.AsSmallComparison.weak W) (AsSmall.up.map f) n
  change F = G
  have ho : ∀ i, F.obj i = G.obj i := by
    intro i
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagExt.object_ext
    · intro j
      change Fin 2 at j
      cases j using Fin.cases <;> rfl
    · intro j
      change Fin 1 at j
      obtain rfl : j = 0 := Subsingleton.elim _ _
      rfl
  apply CategoryTheory.Functor.hext ho
  intro i j a
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagExt.hom_hext (ho i) (ho j)
  intro k
  change Fin 2 at k
  cases k using Fin.cases <;> exact HEq.rfl

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.AsSmallComparison
