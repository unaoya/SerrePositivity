module

public import SerrePositivity.InfinityCategories.HTT.Section5_5_4.StronglySaturatedHom
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.LocalHomOrdinary
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.LocalSaturatedClosure

/-!
概要：生成類に属する局所対象への置換から、生成類と局所同値の一致を導く。
方針：局所性による Hom の持ち上げで置換間の射を作り、その可逆性と二対三則を使う。
規約：局所対象への置換の存在は明示した入力。presentable 圏での構成は別工程。
使われ方：HTT 5.5.4.15 の存在部分から局所同値の特徴づけへの接続。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 強飽和類の辺で各対象を局所対象へ置換できれば、その類は局所同値全体と一致。 -/
lemma stronglySaturated_eq_localEquivalences_of_localReplacements
    {X : SSet.{v}} [Quasicategory X] (smallShape : SSet.{u} → SSet.{v})
    (W S : Set (X _⦋1⦌)) (hS : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FactorizationSystems.IsStronglySaturatedEdgeSetOfShapes smallShape S)
    (hSW : S ⊆ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.localEquivalences W)
    (hreplace : ∀ x : X _⦋0⦌, ∃ (y : X _⦋0⦌)
      (e : Truncated.Edge (X := (truncation 2).obj X) x y),
      e.edge ∈ S ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsLocalObject W y) :
    S = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.localEquivalences W := by
  apply Set.Subset.antisymm hSW
  intro s hs
  let f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex s
  obtain ⟨x', sx, hsx, hx'⟩ := hreplace (X.δ 1 s)
  obtain ⟨y', sy, hsy, hy'⟩ := hreplace (X.δ 0 s)
  have hxl := (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.localEquivalenceHom_iff_edge_mem W sx).mpr (hSW hsx)
  have hyl := (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.localEquivalenceHom_iff_edge_mem W sy).mpr (hSW hsy)
  have hfl : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.LocalEquivalenceHom W (Truncated.HomotopyCategory.homMk f) := hs
  obtain ⟨g, hg⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isLocalForHom_hom_bijective
    (Truncated.HomotopyCategory.homMk sx) (hxl _ hy')).2
      (Truncated.HomotopyCategory.homMk f ≫ Truncated.HomotopyCategory.homMk sy)
  dsimp only at hg
  have hgl : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.LocalEquivalenceHom W g := hxl.cancel_left
    ((congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.LocalEquivalenceHom W) hg).mpr (hfl.comp hyl))
  have hgi : IsIso g := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isIso_of_isLocalForHom_source_target g (hgl _ hx') (hgl _ hy')
  obtain ⟨eg, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective x' y' g
  have heg : eg.edge ∈ S := hS.1 eg hgi
  let k := f.comp sy
  have hk : Truncated.HomotopyCategory.homMk f ≫ Truncated.HomotopyCategory.homMk sy =
      Truncated.HomotopyCategory.homMk k :=
    Truncated.HomotopyCategory.homMk_comp_homMk (Truncated.Edge.compStruct f sy)
  let t : Truncated.Edge.CompStruct sx eg k := _root_.SerrePositivity.InfinityCategories.HTT.Section5_5_4.compStructOfHomotopyCategoryFac (hg.trans hk)
  exact hS.2.2.2.2.2 (Truncated.Edge.compStruct f sy) hsy (hS.2.2.2.1 t hsx heg)

/-- 生成閉包内の局所対象への置換の存在から、生成閉包と元の局所同値の一致を得る。 -/
lemma stronglySaturatedClosure_eq_localEquivalences_of_localReplacements
    {X : SSet.{max u v}} [Quasicategory X] (W : Set (X _⦋1⦌))
    (hX : ∀ (K : SSet.{u}) (p : (SSet.uliftFunctor.{v, u}).obj K ⟶ X), _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit p)
    (hreplace : ∀ x : X _⦋0⦌, ∃ (y : X _⦋0⦌)
      (e : Truncated.Edge (X := (truncation 2).obj X) x y),
      e.edge ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FactorizationSystems.stronglySaturatedClosure (SSet.uliftFunctor.{v, u}).obj W ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsLocalObject W y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FactorizationSystems.stronglySaturatedClosure (SSet.uliftFunctor.{v, u}).obj W = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.localEquivalences W :=
  stronglySaturated_eq_localEquivalences_of_localReplacements _ W _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FactorizationSystems.stronglySaturatedClosure_stronglySaturated _ W)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.stronglySaturatedClosure_subset_localEquivalences W hX) hreplace

/-- 小さい族の生成閉包内で局所置換を構成できれば、その族の局所同値全体は小生成。 -/
lemma localEquivalences_smallGeneration_of_localReplacements
    {X : SSet.{max u v}} [Quasicategory X] {I : Type u} (edges : I → X _⦋1⦌)
    (hX : ∀ (K : SSet.{u}) (p : (SSet.uliftFunctor.{v, u}).obj K ⟶ X), _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit p)
    (hreplace : ∀ x : X _⦋0⦌, ∃ (y : X _⦋0⦌)
      (e : Truncated.Edge (X := (truncation 2).obj X) x y),
      e.edge ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FactorizationSystems.stronglySaturatedClosure (SSet.uliftFunctor.{v, u}).obj (Set.range edges) ∧
        _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsLocalObject (Set.range edges) y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FactorizationSystems.IsOfSmallStrongGeneration (SSet.uliftFunctor.{v, u}).obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.localEquivalences (Set.range edges)) :=
  ⟨I, edges,
    (stronglySaturatedClosure_eq_localEquivalences_of_localReplacements _ hX hreplace).symm⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
