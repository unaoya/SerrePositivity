module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithfulPostcomposition

/-!
概要：充満忠実な後合成による同型の回収は、元の指定同型を厳密に保つ。
方針：ホモトピー圏の充満忠実な関手の同型全単射の両逆則を使う。
規約：同型の存在だけでなく、指定された同型そのものとの一致を記録する。
使われ方：scaffold のテスト同型を回収した後、同じ共同比較へ接続する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FullyFaithfulIsoRecovery

/-- 回収した関手同型を同じ充満忠実な射へ後合成すると、指定された元の同型に戻る。 -/
lemma IsFullyFaithful.preimageFunctorIso_postcomp {X Y K : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {f : X ⟶ Y} (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful f)
    {F G : K ⟶ X} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (F ≫ f) (G ≫ f)) :
    (hf.preimageFunctorIso e).postcomp f = e := by
  apply Iso.ext
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp, eqToIso_refl, Iso.refl_symm, hoFunctor_obj,
    Cat.of_α, hoFunctor_map, Functor.toCatHom_toFunctor, mapHomotopyCategory_obj_mk,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful.preimageFunctorIso, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsFullyFaithful.preimageVertexIso, Iso.trans_refl,
    Iso.trans_hom, Iso.refl_hom, Functor.mapIso_hom, Functor.FullyFaithful.preimageIso_hom,
    Functor.FullyFaithful.map_preimage]
  exact Category.id_comp e.hom

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful export _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FullyFaithfulIsoRecovery.IsFullyFaithful (preimageFunctorIso_postcomp)


/-- 元の関手同型を後合成してから回収すると、同じ元の同型に戻る。 -/
lemma IsFullyFaithful.preimageFunctorIso_of_postcomp {X Y K : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {f : X ⟶ Y} (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful f)
    {F G : K ⟶ X} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F G) :
    hf.preimageFunctorIso (e.postcomp f) = e := by
  apply Iso.ext
  simp [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful.preimageFunctorIso,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsFullyFaithful.preimageVertexIso]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful export _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FullyFaithfulIsoRecovery.IsFullyFaithful (preimageFunctorIso_of_postcomp)


end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FullyFaithfulIsoRecovery
