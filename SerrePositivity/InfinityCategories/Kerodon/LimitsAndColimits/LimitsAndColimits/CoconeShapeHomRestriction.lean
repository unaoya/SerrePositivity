module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeShapeAdjunction
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.PrecompositionMappingPair

/-!
概要：余錐形状の全関手から定値関手への写像空間は、同じ右端への制限で同値となる。
方針：収縮が与える随伴の Hom 全単射を全パラメーターで使う。
規約：元の前合成写像自身の同値性を結論し、任意の比較へ置き換えない。
使われ方：全族の相対始対象性を最終頂点へ反映する。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 全関手から右端の引き戻しへの Hom は、右端への制限の Hom と一対一に対応する。 -/
def coconeShapeHomEquiv (I : SSet.{u}) {X : SSet.{u}}
    (H : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join I (Δ[0] : SSet.{u}) ⟶ X) (G : (Δ[0] : SSet.{u}) ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom H (stdSimplex.isTerminalObj₀.from (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join I Δ[0]) ≫ G) ≃
      _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr I Δ[0] ≫ H) G :=
  ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeShapePrecompositionAdjunction I X).homEquiv
    (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex H)) (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G))).symm

/-- Hom 対応は元の右端制限と、右端の引き戻しの恒等式による輸送からなる。 -/
lemma coconeShapeHomEquiv_apply (I : SSet.{u}) {X : SSet.{u}}
    (H : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join I (Δ[0] : SSet.{u}) ⟶ X) (G : (Δ[0] : SSet.{u}) ⟶ X)
    (a : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom H (stdSimplex.isTerminalObj₀.from (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join I Δ[0]) ≫ G)) :
    coconeShapeHomEquiv I H G a =
      (hoFunctor.map ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr I (Δ[0] : SSet.{u}))).app X)).toFunctor.map a ≫
        eqToHom (congrArg (fun q ↦ HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex q))
          (show _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr I Δ[0] ≫ (stdSimplex.isTerminalObj₀.from (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join I Δ[0]) ≫ G) = G
            from by rw [← Category.assoc,
              stdSimplex.isTerminalObj₀.hom_ext (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr I Δ[0] ≫ _) (𝟙 _),
              Category.id_comp])) := by
  change _ ≫ (eqToHom (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.retractionPrecomposition_retraction _ _
      (stdSimplex.isTerminalObj₀.hom_ext _ _) X)).app
    (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G)) = _
  rw [eqToHom_app]

/-- 右端へ制限する元の Hom 写像は、標的が右端からの引き戻しなら全単射。 -/
lemma coconeShapeHomRestriction_bijective (I : SSet.{u}) {X : SSet.{u}}
    (H : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join I (Δ[0] : SSet.{u}) ⟶ X) (G : (Δ[0] : SSet.{u}) ⟶ X) :
    Function.Bijective ((hoFunctor.map ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr I (Δ[0] : SSet.{u}))).app X)).toFunctor.map :
      _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom H (stdSimplex.isTerminalObj₀.from (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join I Δ[0]) ≫ G) → _) := by
  let e := coconeShapeHomEquiv I H G
  let t := eqToIso (congrArg (fun q ↦ HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex q))
    (show _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr I Δ[0] ≫ (stdSimplex.isTerminalObj₀.from (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join I Δ[0]) ≫ G) = G from by
      rw [← Category.assoc,
        stdSimplex.isTerminalObj₀.hom_ext (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr I Δ[0] ≫ _) (𝟙 _), Category.id_comp]))
  have he : Function.Bijective (fun a : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom H
      (stdSimplex.isTerminalObj₀.from (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join I Δ[0]) ≫ G) ↦
      (hoFunctor.map ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr I (Δ[0] : SSet.{u}))).app X)).toFunctor.map a ≫ t.hom) := by
    exact (show (fun a ↦ e a) = _ from funext (coconeShapeHomEquiv_apply I H G)) ▸ e.bijective
  exact he.of_comp_left (fun _ _ h ↦ (cancel_mono t.hom).mp h)

/-- 右端制限の指定 pinched 比較は、標的が定値ならホモトピー同値。 -/
lemma coconeShapeRight_pinchedHomMap_equivalence (I : SSet.{u}) {X : SSet.{u}}
    [Quasicategory X] (H : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join I (Δ[0] : SSet.{u}) ⟶ X) (G : (Δ[0] : SSet.{u}) ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr I Δ[0])).app X)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex H) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (stdSimplex.isTerminalObj₀.from (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join I Δ[0]) ≫ G))) :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.precomposition_pinchedHomMap_equivalence_of_constantFamily _ H _
    (fun A ↦ coconeShapeHomRestriction_bijective I (H ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap A X)
      (G ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap A X))

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
