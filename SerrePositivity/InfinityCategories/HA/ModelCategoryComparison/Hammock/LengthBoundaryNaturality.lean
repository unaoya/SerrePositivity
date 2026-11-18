module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LengthBoundaryLift
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LengthNaturality

/-!
# 元の境界と貼り合わせ射の図式の比較への自然性

概要：元の自然変換は境界の像の和に作用し、包含と前段階への貼り合わせ射を保つ。
方針：元の短い語による表示を同じ自然変換で移し、元の標準射上で照合する。
規約：境界の比較は元の全体の比較射の制限であり、任意の同型で代用しない。
使われ方：proper 図式の境界と段階の弱同値の比較。
-/

@[expose] public section
universe w
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock
open _root_.CategoryTheory

variable {F G : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word ⥤ SSet.{w}} (η : F ⟶ G)

def _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.BoundaryPresentation.map {n : ℕ} {c : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {k : SimplexCategoryᵒᵖ}
    {x : (F.obj c).obj k} (p : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.BoundaryPresentation F n c k x) :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.BoundaryPresentation G n c k ((η.app c).app k x) where
  source := p.source
  bound := p.bound
  arrow := p.arrow
  injective := p.injective
  simplex := (η.app p.source).app k p.simplex
  image := by
    have he := congrArg (fun θ => θ.app k p.simplex) (η.naturality p.arrow)
    change (η.app c).app k ((F.map p.arrow).app k p.simplex) =
      (G.map p.arrow).app k ((η.app p.source).app k p.simplex) at he
    rw [p.image] at he
    exact he.symm

def lengthBoundaryMap (n : ℕ) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) :
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.lengthBoundary F n c).toFunctor ⟶ (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.lengthBoundary G n c).toFunctor where
  app k := ↾fun x => ⟨(η.app c).app k x.val,
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.lengthBoundary_mem_iff G n c k _).2
      ⟨_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.BoundaryPresentation.map η (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.boundaryPresentation F n c k x)⟩⟩
  naturality k l α := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    exact NatTrans.naturality_apply (η.app c) α x.val

lemma lengthBoundaryMap_ι (n : ℕ) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.lengthBoundaryMap η n c ≫ (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.lengthBoundary G n c).ι =
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.lengthBoundary F n c).ι ≫ η.app c := rfl

lemma lengthBoundaryMap_lift (n : ℕ) {a c : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (ha : a.length ≤ n)
    (f : a ⟶ c) (hf : Function.Injective f.orderHom) :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.lengthBoundaryLift F n ha f hf ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.lengthBoundaryMap η n c =
      η.app a ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.lengthBoundaryLift G n ha f hf := by
  apply NatTrans.ext
  funext k
  apply ConcreteCategory.hom_ext
  intro σ
  apply Subtype.ext
  exact congrArg (fun θ => θ.app k σ) (η.naturality f)

lemma lengthBoundaryMap_attach (hF : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ProperDiagram F) (hG : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ProperDiagram G)
    (n : ℕ) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.lengthBoundaryMap η n c ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.lengthBoundaryToStage hG n c =
      _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.lengthBoundaryToStage hF n c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageMap η n := by
  apply NatTrans.ext
  funext k
  apply ConcreteCategory.hom_ext
  intro x
  let p := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.boundaryPresentation F n c k x
  have hp := (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.BoundaryPresentation.map η p).image
  change (G.map p.arrow).app k ((η.app p.source).app k p.simplex) =
    ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.lengthBoundaryMap η n c).app k x).val at hp
  have hv := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.lengthBoundaryStageValue_eq hG n c k ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.lengthBoundaryMap η n c).app k x)
    p.bound p.arrow p.injective ((η.app p.source).app k p.simplex) hp
  have hi := congrArg (fun θ => θ.app k p.simplex)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageInclusion_map η n p.source p.bound)
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageMap η n).app k
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageInclusion F n p.source p.bound).app k p.simplex) =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageInclusion G n p.source p.bound).app k ((η.app p.source).app k p.simplex) at hi
  change _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.lengthBoundaryStageValue G n c k ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.lengthBoundaryMap η n c).app k x) =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageMap η n).app k (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.lengthBoundaryStageValue F n c k x)
  rw [hv, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.lengthBoundaryStageValue_eq hF n c k x p.bound p.arrow p.injective p.simplex p.image]
  exact hi.symm

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock
