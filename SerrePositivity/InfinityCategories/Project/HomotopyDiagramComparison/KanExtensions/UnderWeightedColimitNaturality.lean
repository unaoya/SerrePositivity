module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.KanExtensions.UnderWeightedColimitNormalization
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialReplacementFunctor

/-!
概要：同じ Under coend の指定比較射は、係数図式の全ての射に自然。
方針：既存の係数の自然性を Under 評価で使い、coend の普遍脚の外延性で戻す。
規約：Kerodon Construction 5.3.2.1（Tag 035V）の既存模型の自然性の法則。
使われ方：Čech の元の増大を保つ、反転 BK coend と元の圏の比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
variable {I : Type u} [SmallCategory I] {F G : I ⥤ SSet.{u}}

/-- 元の各普遍脚での評価は、同じ係数変換と可換。 -/
lemma underWeightedColimitLeg_naturality (η : F ⟶ G) (i : I) :
    η.app i ▷ nerve (Under i) ≫ underWeightedColimitLeg G i =
      underWeightedColimitLeg F i ≫ simplicialReplacementMap η := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨x, τ⟩
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  change SSet.yonedaEquiv.symm ((η.app i).app (Opposite.op ⦋n⦌) x) ≫
    G.map (τ.obj 0).hom = (SSet.yonedaEquiv.symm x ≫ F.map (τ.obj 0).hom) ≫
      η.app (τ.obj 0).right
  rw [← SSet.yonedaEquiv_symm_comp, Category.assoc, ← η.naturality, ← Category.assoc]

/-- 既に構成した同じ大域比較射は、係数図式の全ての自然変換と可換。 -/
lemma underWeightedColimitToReplacement_naturality (η : F ⟶ G) :
    weightedColimitMap (underNerveWeight I) η ≫ underWeightedColimitToReplacement G =
      underWeightedColimitToReplacement F ≫ simplicialReplacementMap η := by
  apply weightedColimit_hom_ext
  intro i
  rw [← Category.assoc, weightedColimitι_map, Category.assoc,
    underWeightedColimitToReplacement_ι, ← Category.assoc,
    underWeightedColimitToReplacement_ι]
  exact underWeightedColimitLeg_naturality η i

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
