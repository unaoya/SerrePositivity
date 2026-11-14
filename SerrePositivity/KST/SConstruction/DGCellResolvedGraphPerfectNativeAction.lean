module
public import SerrePositivity.KST.SConstruction.DGCellResolvedGraphPerfectNerveArrow
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Actions.DGModuleDerivedFunctor
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.SimplicialFunctors.FunctorHomWhiskerMapTransport

/-!
概要：同じ Perf 比較射の native 導来延長作用を元 graph 比較の作用と全体で照合する。
方針：元包含射の型付き同定を実導来延長で後合成し、元関手圏の射を回収する。
規約：元 graph 比較と指定 dg 射を保持。使われ方：共通 Perf 比較族と native square の接続。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (B E : Type (max (u + 1) v))
  [DGCategory R B] [Small.{u} B] [DGCategory R E] [Small.{u} E]
local notation "P" => DGCategoryCellResolution.Source R B
local notation "J" => perfectDGModuleInclusion R (P) Set.univ
local notation "ρ" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R (RightModule R (P)) (P)
  (DGFunctor.id (RightModule R (P)))
local notation "I" => dgFullSubcategoryInclusion R (RightModule R E) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleSemifreeProperty R E)

/-- 概要：元 graph 全関手射を同じ実導来延長と生包含で後合成する。
方針：同じ元関手圏の実作用を合成する。規約：元の指定 dg 射を保持。
使われ方：同じ Perf 比較射の native 作用の正本。 -/
def dgCellGraphExtendedNativeFunctor (projection : DGFunctor R (P) E) :
    BimoduleCategory R (P) (P) ⥤
      hoFunctor.obj ((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (P))).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R E))) :=
  dgCellGraphNativeFunctor R B ⋙ SSet.mapHomotopyCategory
    ((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (P))).map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleExtensionInfinity R (P) E projection ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (I)))

/-- 概要：共通 Perf 比較族での元射の作用は元 graph の同じ実 native 作用。
方針：包含同定と二段後合成の交換を貼る。規約：全関手射の値を保持。
使われ方：二成分比較と native square を同じ中央射で接続する。 -/
lemma dgCellResolvedGraphPerfectNativeAction_heq (F G : DGFunctor R B B)
    (τ : DGFunctorParamTrans R B B (𝟙_ (Complex R)) F G)
    (projection : DGFunctor R (P) E) :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgCellResolvedGraphPerfectFunctor R B F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellResolvedGraph_projective R B F)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgCellResolvedGraphPerfectFunctor R B G (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellResolvedGraph_projective R B G)))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (J) ≫ (ρ)) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleExtensionInfinity R (P) E projection ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (I))
      (dgCellResolvedGraphPerfectNerveArrow R B F G τ))
      ((dgCellGraphExtendedNativeFunctor R B E projection).map (dgCellResolvedGraphMap R B F G τ)) := by
  let f := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgCellResolvedGraphPerfectFunctor R B F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellResolvedGraph_projective R B F))
  let g := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgCellResolvedGraphPerfectFunctor R B G (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellResolvedGraph_projective R B G))
  let a := dgCellResolvedGraphPerfectNerveArrow R B F G τ
  let m := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleFunctorHomFunctor R (P) (P)).map (dgCellResolvedGraphMap R B F G τ)
  let K := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleExtensionInfinity R (P) E projection ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (I)
  have hF : f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (J) = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgCellResolvedGraphModuleFunctor R B F) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp _ _).symm.trans (congrArg (fun L => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map L)
      (dgCellResolvedGraphPerfectFunctor_inclusion R B F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellResolvedGraph_projective R B F)))
  have hG : g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (J) = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgCellResolvedGraphModuleFunctor R B G) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp _ _).symm.trans (congrArg (fun L => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map L)
      (dgCellResolvedGraphPerfectFunctor_inclusion R B G (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellResolvedGraph_projective R B G)))
  have h₀ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp_heq_of_target_eq a (Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (J)) (ρ) K)
  have h₁ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp_postcomp f g (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (J)) ((ρ) ≫ K) a
  have h₂ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp_heq _ m hF hG
    (dgCellResolvedGraphPerfectNerveArrow_inclusion R B F G τ) ((ρ) ≫ K)
  have h₃ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp_postcomp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgCellResolvedGraphModuleFunctor R B F))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgCellResolvedGraphModuleFunctor R B G)) (ρ) K m
  exact h₀.trans ((heq_of_eq h₁).symm.trans (h₂.trans (heq_of_eq h₃).symm))

end SerrePositivity.KST.SConstruction
