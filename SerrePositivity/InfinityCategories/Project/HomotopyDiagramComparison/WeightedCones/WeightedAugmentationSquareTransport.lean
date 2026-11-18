module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoconeComparison.WeightedColimitAugmentation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PrecompositionTensor
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.WeakHomotopy

/-!
概要：同じ重みの増大の弱同値性を、係数と頂点の指定同型の可換四角形で移す。
方針：既存 coend 関手の同型の像、元の増大の自然性、弱同値の二対三則を使う。
規約：Kerodon §7.5（Tag 039Y）の既存模型の係数移送の法則。Kan 性を追加しない。
使われ方：S8 の Yoneda の同じ全自然同型による評価の移送。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits SSet
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Project.FilteredExchange
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
variable {I : Type u} [SmallCategory I] {F G : I ⥤ SSet.{u}}

/-- 元の全余錐の指定四角形に沿って、同じ増大の弱同値性を移す。 -/
lemma weightedAugmentation_weak_of_iso_square (W : Iᵒᵖ ⥤ SSet.{u})
    (cF : Cocone F) (cG : Cocone G) (e : F ≅ G) (b : cF.pt ≅ cG.pt)
    (he : ∀ i, cF.ι.app i ≫ b.hom = e.hom.app i ≫ cG.ι.app i)
    (hc : IsWeakHomotopyEquivalence (weightedColimitAugmentation W cF)) :
    IsWeakHomotopyEquivalence (weightedColimitAugmentation W cG) := by
  have hm := (isPrecompositionEquivalence_of_iso ((weightedColimitFunctor W).mapIso e)).isWeakHomotopyEquivalence
  have hb := (isPrecompositionEquivalence_of_iso b).isWeakHomotopyEquivalence
  have h := weightedColimitAugmentation_naturality W e.hom cF cG b.hom he
  exact hm.cancel_left (h ▸ hc.comp hb)

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
