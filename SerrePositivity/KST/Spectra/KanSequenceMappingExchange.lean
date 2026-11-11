module

public import SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeMappingStrength
public import SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeRestriction
public import SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeSymmetry
public import SerrePositivity.KST.Spectra.KanSequenceMappingFunctor

/-!
概要：二重 mapping 列のパラメータ交換を、同じ段交換を持つ厳密な列同型へ束ねる。
方針：strength の交換則と標的自然性で構造条件を証明し、逆順の交換を逆射に使う。
規約：パラメータの Kan 性不要。使われ方：源の全列区間のパラメータ作用への移送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed
namespace SerrePositivity.KST.Spectra.KanSequence

/-- 元の内部 Hom の段交換を持つ、二重 mapping 列の厳密な射。 -/
def mappingExchange (A K : PointedSimplicialSet.{u}) (X : KanSequence.{u}) :
    Hom (mapping A (mapping K X)) (mapping K (mapping A X)) where
  app n := (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso A K (X.level n).space).hom
  comm n := by
    change PointedSimplicialSet.circle.{u} ◁
        (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso A K (X.level n).space).hom ≫
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.map PointedSimplicialSet.circle.{u} K ((ihom A).obj (X.level n).space) ≫
        (ihom K).map (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.map PointedSimplicialSet.circle.{u} A (X.level n).space ≫
          (ihom A).map (X.sigma n))) =
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.map PointedSimplicialSet.circle.{u} A ((ihom K).obj (X.level n).space) ≫
      (ihom A).map (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.map PointedSimplicialSet.circle.{u} K (X.level n).space ≫
        (ihom K).map (X.sigma n))) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso A K (X.level (n + 1)).space).hom
    simp only [Functor.map_comp, Category.assoc]
    rw [← _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.mapping_strength_assoc, ← _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeTarget.natural_post]

/-- 二重 mapping 列の交換は、同じ標的の列射について厳密に自然。 -/
lemma mappingExchange_natural (A K : PointedSimplicialSet.{u})
    {X Y : KanSequence.{u}} (p : Hom X Y) :
    (mappingPost A (mappingPost K p)).comp (mappingExchange A K Y) =
      (mappingExchange A K X).comp (mappingPost K (mappingPost A p)) := by
  apply Hom.ext_app
  intro n
  exact _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeTarget.natural_post A K (p.app n)

/-- 逆順の同じ交換を逆射に持つ、二重 mapping 列の厳密な同型。 -/
def mappingExchangeIso (A K : PointedSimplicialSet.{u}) (X : KanSequence.{u}) :
    mapping A (mapping K X) ≅ mapping K (mapping A X) where
  hom := mappingExchange A K X
  inv := mappingExchange K A X
  hom_inv_id := by
    apply Hom.ext_app
    intro n
    change (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso A K (X.level n).space).hom ≫
      (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso K A (X.level n).space).hom = 𝟙 _
    rw [_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.hom_eq_inv K A, Iso.hom_inv_id]
  inv_hom_id := by
    apply Hom.ext_app
    intro n
    change (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso K A (X.level n).space).hom ≫
      (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso A K (X.level n).space).hom = 𝟙 _
    rw [_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.hom_eq_inv A K, Iso.hom_inv_id]

/-- 外側の元のパラメータへの制限も、列全体の同じ交換と厳密に可換。 -/
lemma mappingExchange_pre_left {A' A : PointedSimplicialSet.{u}} (i : A' ⟶ A)
    (K : PointedSimplicialSet.{u}) (X : KanSequence.{u}) :
    (mappingPre i (mapping K X)).comp (mappingExchange A' K X) =
      (mappingExchange A K X).comp (mappingPost K (mappingPre i X)) := by
  apply Hom.ext_app
  intro n
  change _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i (PointedObject.basedHom K (X.level n).space) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso A' K (X.level n).space).hom =
    (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso A K (X.level n).space).hom ≫
      (ihom K).map (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i (X.level n).space)
  simpa only [← _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre,
    PointedObject.ihom_obj_eq_basedHom] using
    _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeNaturality.natural_pre_left i K (X.level n).space

/-- 内側の元のパラメータへの制限も、列全体の同じ交換と厳密に可換。 -/
lemma mappingExchange_pre_right (A : PointedSimplicialSet.{u})
    {K' K : PointedSimplicialSet.{u}} (i : K' ⟶ K) (X : KanSequence.{u}) :
    (mappingPost A (mappingPre i X)).comp (mappingExchange A K' X) =
      (mappingExchange A K X).comp (mappingPre i (mapping A X)) := by
  apply Hom.ext_app
  intro n
  change (ihom A).map (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i (X.level n).space) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso A K' (X.level n).space).hom =
    (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso A K (X.level n).space).hom ≫
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i (PointedObject.basedHom A (X.level n).space)
  simpa only [← _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre,
    PointedObject.ihom_obj_eq_basedHom] using
    _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeSecondSource.natural_pre_right A i (X.level n).space

end SerrePositivity.KST.Spectra.KanSequence
