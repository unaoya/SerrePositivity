module
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.HomotopyInvertibility
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SpanHomotopyGluing
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PushoutHomotopy

/-! # span の比較の二枝による可逆性判定

概要：二つの枝で可逆な span の比較ホモトピーは全体でも可逆である。
方針：ホーンの pushout と点ごとの可逆性の既存の判定を使う。
規約：指定ホモトピー自体の可逆性を示す。使われ方：cofiber 図式の同型不変性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：二枝への制限が可逆な span のホモトピーは可逆。
方針：各枝での可逆性を頂点ごとの可逆性に戻し、pushout の頂点被覆を適用する。
規約：値域は quasicategory。使われ方：最初の二成分が同型である cofiber の比較。 -/
lemma spanHomotopy_isInvertible_of_branches {X : SSet.{u}} [Quasicategory X]
    {F G : (horn 2 0 : SSet.{u}) ⟶ X} (H : SSet.Homotopy F G)
    (L : SSet.Homotopy (horn₂₀.ι₀₁ ≫ F) (horn₂₀.ι₀₁ ≫ G))
    (R : SSet.Homotopy (horn₂₀.ι₀₂ ≫ F) (horn₂₀.ι₀₂ ≫ G))
    (hL : (horn₂₀.ι₀₁ ▷ (Δ[1] : SSet.{u})) ≫ H.h = L.h)
    (hR : (horn₂₀.ι₀₂ ▷ (Δ[1] : SSet.{u})) ≫ H.h = R.h)
    (hLi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy L))
    (hRi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy R)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.functorEdgeOfSimplicialHomotopy_isInvertible_of_pointwise H
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pushoutHomotopy_isInvertible horn₂₀.isPushout H L R hL hR
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.homotopyVertex_isInvertible_of_functorEdge L hLi)
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.homotopyVertex_isInvertible_of_functorEdge R hRi))

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
