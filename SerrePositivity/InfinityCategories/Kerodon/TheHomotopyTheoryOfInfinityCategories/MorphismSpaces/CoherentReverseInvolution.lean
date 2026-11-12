module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentDoubleOpposite

/-!
概要：標準 thickening の二回の頂点と path の反転の往復則。
方針：対象では Fin.rev を二回適用し、Hom では部分集合の二回の像と端点の移送を計算する。
規約：二重反対から元の豊穣圏への標準関手を最後に合成する。
使われ方：Kerodon §4.6.7（Tag 01LA） の反対の coherent nerve の標準射の逆の検証。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet SimplicialThickening
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：標準 thickening の頂点と path を二回反転すると恒等豊穣関手になる。
方針：対象の rev の往復則の後で、Hom の端点の移送を保ちつつ二回の集合の像を消去する。
規約：反対の豊穣圏の二重 unop を明示して合成する。
使われ方：Kerodon §4.6.7（Tag 01LA） の反対の coherent simplex の往復則。 -/
lemma coherentReverseThickening_involution (n : ℕ) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentReverseThickening n).comp SSet
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentEnrichedFunctorOp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentReverseThickening n))).comp SSet
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentEnrichedDoubleUnop (SimplicialThickening (ULift.{u} (Fin (n + 1))))) =
      EnrichedFunctor.id SSet (SimplicialThickening (ULift.{u} (Fin (n + 1)))) := by
  let J := ULift.{u} (Fin (n + 1))
  let D := SimplicialThickening J
  let F := ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentReverseThickening n).comp SSet
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentEnrichedFunctorOp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentReverseThickening n))).comp SSet
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentEnrichedDoubleUnop D)
  have hobj : ∀ i : D, F.obj i = i := by
    intro i
    have hi : (ULift.up i.as.down.rev.rev : J) = i.as := by
      apply ULift.ext
      exact Fin.rev_rev i.as.down
    exact congrArg (fun a : J ↦ (⟨a⟩ : D)) hi
  refine EnrichedFunctor.ext SSet hobj (fun i j => ?_)
  change F.map i j ≫
    eqToHom (congrArg₂ (fun a b : D ↦ SimplicialCategory.sHom a b) (hobj i) (hobj j)) = 𝟙 _
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro P
  apply CategoryTheory.Functor.ext (fun k => ?_)
  apply SimplicialThickening.Path.ext
  change (((eqToHom (congrArg₂ (fun a b : D ↦ SimplicialCategory.sHom a b)
    (hobj i) (hobj j))).app d ((F.map i j).app d P)).obj k).I = (P.obj k).I
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.thickeningHom_transport_I (hobj i) (hobj j) ((F.map i j).app d P) k]
  change (fun a : J ↦ (ULift.up a.down.rev : J)) ''
    ((fun a : J ↦ (ULift.up a.down.rev : J)) '' (P.obj k).I) = (P.obj k).I
  rw [Set.image_image]
  have hrev : (fun a : J ↦ (ULift.up a.down.rev.rev : J)) = id := by
    funext a
    apply ULift.ext
    exact Fin.rev_rev a.down
  rw [hrev, Set.image_id]

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
