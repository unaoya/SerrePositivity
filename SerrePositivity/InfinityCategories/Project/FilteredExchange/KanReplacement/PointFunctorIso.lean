module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinTensorPoint
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.ConstantDiagram

/-!
概要：点上の定値図式関手は厳密な同型。
方針：第二射影の同型性と内部 Hom 随伴で全パラメータの射を比較する。
規約：標準零単体をモノイダル単位と定義的に同一視しない。
使われ方：内部 Hom への対角を実際の二項積の対角へ戻す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 概要：標準点上の定値図式関手は同型。
方針：全パラメータでの uncurry は同型な第二射影による前合成になる。
規約：標的の充填性は不要。使われ方：二項対角関手の厳密な表示。 -/
instance constantDiagram_point_isIso (X : SSet.{u}) :
    IsIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.constantDiagram (Δ[0] : SSet.{u}) X) := by
  apply isIso_of_yoneda_map_bijective
  intro T
  constructor
  · intro f g h
    have hh := congrArg uncurry h
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.uncurry_comp_constantDiagram, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.uncurry_comp_constantDiagram] at hh
    exact (cancel_epi (snd (Δ[0] : SSet.{u}) T)).1 hh
  · intro g
    refine ⟨inv (snd (Δ[0] : SSet.{u}) T) ≫ uncurry g, ?_⟩
    apply uncurry_injective
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.uncurry_comp_constantDiagram, ← Category.assoc, IsIso.hom_inv_id, Category.id_comp]

/-- 概要：点上の関手の標準同型。
方針：定値図式関手の同型性を使う。
規約：hom は元の定値図式そのもの。使われ方：積の対角の cofinality。 -/
def pointFunctorIso (X : SSet.{u}) : X ≅ (ihom (Δ[0] : SSet.{u})).obj X :=
  asIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.constantDiagram (Δ[0] : SSet.{u}) X)

end SerrePositivity.InfinityCategories.Project.FilteredExchange
