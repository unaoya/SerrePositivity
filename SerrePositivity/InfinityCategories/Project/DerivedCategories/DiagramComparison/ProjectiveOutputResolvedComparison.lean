module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.SpecifiedProjectiveCocone
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleResolvedProjectiveComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithfulPostcomposition

/-!
概要：既に射影的な一点加群を出力する関手の実分解を、指定射影的模型へ比較する。
方針：元のaugmentation比較を充満忠実な包含で戻し、半自由・射影的比較の逆を後合成する。
規約：入力は全dg圏のまま、全関手同型を作る。対象ごとの分解の選択ではない。
使われ方：3b-3 R6、元の直和実現の評価と3b-1の指定頂点の比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison

variable (A : Type u) [CommRing A] (C : Type (u + 1)) [DGCategory A C]
  (F : DGFunctor A C (ProjectiveDGModules A PUnit.{1}))

/-- 射影的出力の分解を射影的模型へ戻すと、元の同じdg関手と全関手同型。 -/
def projectiveOutputResolvedIso :
    FunctorIso
      (dgModuleResolvedInfinity A C PUnit.{1}
          (F.comp (dgFullSubcategoryInclusion A (RightModule A PUnit.{1})
            (dgModuleProjectiveProperty A PUnit.{1}))) ≫
        SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
          (dgSemifreeToProjective A PUnit.{1}))
      (SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F) := by
  let I := dgFullSubcategoryInclusion A (RightModule A PUnit.{1})
    (dgModuleProjectiveProperty A PUnit.{1})
  let J := dgFullSubcategoryInclusion A (RightModule A PUnit.{1})
    (dgModuleSemifreeProperty A PUnit.{1})
  have hc : (dgSemifreeToProjective A PUnit.{1}).comp I = J := by
    refine EnrichedFunctor.ext (Complex A) (fun _ => rfl) ?_
    intro X Y
    simp [I, J, dgSemifreeToProjective, dgFullSubcategoryInclusion, EnrichedFunctor.comp_map]
  have e := dgModuleResolvedInfinity_inclusionIso A C PUnit.{1} (F.comp I)
    (fun X => (F.obj X).property)
  apply (dgFullSubcategoryInclusionNerve_isFullyFaithful A (RightModule A PUnit.{1})
    (dgModuleProjectiveProperty A PUnit.{1})).preimageFunctorIso
  simpa only [Category.assoc,
    ← SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp,
    hc] using! e

/-- 既存の同じD(A)へ送ると、分解評価と指定射影的模型の評価は全関手同型。 -/
def projectiveOutputResolvedPointIso :
    FunctorIso
      (dgModuleResolvedInfinity A C PUnit.{1}
          (F.comp (dgFullSubcategoryInclusion A (RightModule A PUnit.{1})
            (dgModuleProjectiveProperty A PUnit.{1}))) ≫
        (semifreePointEquivalence A).hom)
      (SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F ≫
        (projectivePointEquivalence A).hom) := by
  let e := (dgSemifreeToProjectiveNerve_isQCatEquivalence A PUnit.{1}).choose
  let L := dgModuleResolvedInfinity A C PUnit.{1}
    (F.comp (dgFullSubcategoryInclusion A (RightModule A PUnit.{1})
      (dgModuleProjectiveProperty A PUnit.{1})))
  have h0 : FunctorIso (L ≫ 𝟙 _)
      (SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F ≫ e.inv) :=
    (e.homInvIso.precomp L).symm ≪≫
      (projectiveOutputResolvedIso A C F).postcomp e.inv
  have h := h0.postcomp (semifreePointEquivalence A).hom
  simpa only [projectivePointEquivalence, e, L, Category.assoc, Category.comp_id] using! h

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
