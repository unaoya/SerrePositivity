module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalFunctorHom
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedComposition

/-!
概要：元の単体的関手の区間 Hom 作用と前合成は、全自然同型で可換。
方針：元の h Fun の後合成と定値関手の作用の計算を行う。
規約：元のホモトピー圏の任意の射を扱う。模型変更の同値も元の比較射で判定する。
使われ方：写像空間の retract 正方形から相対始対象性を戻す。

対応節は Kerodon 8.5（Tag 03Y9）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents

/-- 元の任意の射の類による前合成と、元の関手の全区間 Hom 作用は全自然同型で可換。 -/
def intervalFunctorMap_precomposeHoIso {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (p : X ⟶ Y) {a b : X _⦋0⦌}
    (γ : (HomotopyCategory.mk a : hoFunctor.obj X) ⟶ HomotopyCategory.mk b)
    (z : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalPrecompose z γ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFunctorMap p a z)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFunctorMap p b z ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalPrecompose (p.app (Opposite.op ⦋0⦌) z)
        ((hoFunctor.map p).toFunctor.map γ)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorIsoOfSimplicialHomotopy
  apply Classical.choice
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom_eq_imp_homotopy
  let K := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace b z
  have hconst := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap_postcomp K p γ
  have hc := congrArg (fun t ↦ t ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.constantFunctorCompIso K b p).inv) hconst
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at hc
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalFunctorMap_familyHom, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalPrecompose_hom, Functor.map_comp,
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalPrecompose_family]
  have hm := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalFunctorMap_familyHom (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace b z)) p
  simp only [Category.id_comp] at hm
  rw [hm]
  have h := congrArg (fun t ↦ t ≫
    (hoFunctor.map ((ihom K).map p)).toFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (𝟙 K)) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.constantFunctorCompIso K z p).hom) hc
  simp only [Category.assoc] at h ⊢
  exact h

/-- 元の pinched Hom 比較が同値であることと、元の区間 Hom 比較の同値性は同値。 -/
lemma pinchedHomMap_equivalence_iff_intervalFunctorMap {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (p : X ⟶ Y) (x y : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap p x y) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFunctorMap p x y) := by
  have hx := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace_isQCatEquivalence x y
  have hy := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace_isQCatEquivalence
    (p.app (Opposite.op ⦋0⦌) x) (p.app (Opposite.op ⦋0⦌) y)
  constructor
  · intro h
    have hh := h.comp hy
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.pinchedIntervalComparison_naturality] at hh
    exact hx.cancel_left hh
  · intro h
    have hh := hx.comp h
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.pinchedIntervalComparison_naturality] at hh
    exact hy.cancel_right hh

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents
