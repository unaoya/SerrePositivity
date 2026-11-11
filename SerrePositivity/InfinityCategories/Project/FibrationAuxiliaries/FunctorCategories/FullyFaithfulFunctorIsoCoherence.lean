module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithfulPostcomposition

/-!
概要：充満忠実な射への後合成は、元の関手同型の等式と逆像の coherence を反映する。
方針：関手空間のホモトピー圏の充満忠実性と、同じ逆像の射の法則を使う。
規約：同型の存在だけでなく、指定された同型そのものの一致を検査する。
使われ方：元の分類作用と局所自然性の共有頂点での三角形の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FullyFaithfulFunctorIsoCoherence

/-- 充満忠実な射で戻した同じ頂点同型の像は、元の指定同型そのもの。 -/
lemma IsFullyFaithful.preimageVertexIso_map {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {f : X ⟶ Y} (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful f)
    {x y : X _⦋0⦌} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (f.app _ x) (f.app _ y)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map (hf.preimageVertexIso e) f = e := by
  apply Iso.ext
  exact hf.toHoFullyFaithful.map_preimage
    (X := SSet.HomotopyCategory.mk x) (Y := SSet.HomotopyCategory.mk y) e.hom

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful export _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FullyFaithfulFunctorIsoCoherence.IsFullyFaithful (preimageVertexIso_map)


/-- 同じ関手同型の充満忠実な後合成による逆像は、元の指定同型を厳密に回収する。 -/
lemma IsFullyFaithful.preimageFunctorIso_postcomp {X Y K : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {f : X ⟶ Y} (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful f)
    {F G : K ⟶ X} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (F ≫ f) (G ≫ f)) :
    (hf.preimageFunctorIso e).postcomp f = e := by
  apply Iso.ext
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp, Iso.trans_hom, Iso.symm_hom, eqToIso.hom, eqToIso.inv, eqToHom_refl,
    Category.id_comp, Category.comp_id, CategoryTheory.Functor.mapIso_hom]
  exact (hf.postcompose K).toHoFullyFaithful.map_preimage
    (X := SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F))
    (Y := SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G)) e.hom

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful export _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FullyFaithfulFunctorIsoCoherence.IsFullyFaithful (preimageFunctorIso_postcomp)


/-- 指定された二つの関手同型は、充満忠実な射への後合成後に等しければ等しい。 -/
lemma IsFullyFaithful.postcomp_functorIso_injective {X Y K : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {f : X ⟶ Y} (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful f)
    {F G : K ⟶ X} (e e' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F G) (h : e.postcomp f = e'.postcomp f) : e = e' := by
  apply Iso.ext
  apply (hf.postcompose K).toHoFullyFaithful.map_injective
  have hh := congrArg Iso.hom h
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp, Iso.trans_hom, Iso.symm_hom, eqToIso.hom, eqToIso.inv, eqToHom_refl,
    Category.id_comp, Category.comp_id, CategoryTheory.Functor.mapIso_hom] using hh

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful export _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FullyFaithfulFunctorIsoCoherence.IsFullyFaithful (postcomp_functorIso_injective)


end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FullyFaithfulFunctorIsoCoherence
