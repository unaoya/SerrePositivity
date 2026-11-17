module

public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleProbeComparisonMap
public import SerrePositivity.EInfinity.Modules.LocalizationComparisonEvaluation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.FunctorComparisons.ClosedNerveFunctorNaturality

/-!
# 同じ K の probe 全通常 nerve 上の三角比較

概要：M10 の元の probe 全包含に沿う同じ K の比較を、全通常鎖の関手同型として保持する。
方針：同じ宇宙表示・閉零鎖の dg 単体化・同じ解像度 retract を合成する。
規約：HA Construction 1.3.1.9、元の全通常鎖を保持する。
使われ方：同じ K の全 Hom 誘導射と frame の評価円柱の照合。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Opposite SSet
open SerrePositivity.DifferentialGraded SerrePositivity.EInfinity.Modules
open _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
open SerrePositivity.InfinityCategories.HA.Section7_1_1
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories
open DifferentialGradedCategories
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open scoped Simplicial
variable (A : Type u) [CommRing A]

/-- 概要：同じ probe 閉零圏を同じ局所化源の Hom 宇宙に置く。
方針：既存の ULiftHom だけを適用する。
規約：HA Construction 1.3.1.9、元の対象。使われ方：全通常 nerve の同じ入力。 -/
abbrev strictRawModuleLiftedProbeCategory (X : (operad A).Algebra) : Type (u + 1) :=
  ULiftHom.{u + 1} (strictRawModuleProbeCategory A X)

/-- 概要：同じ probe 全包含を同じ通常相対圏の宇宙へ送る全関手。
方針：元の二つの ULiftHom 関手と同じ包含を合成する。
規約：HA Construction 1.3.1.9、全通常射。使われ方：同じ K の全鎖の制限。 -/
def strictRawModuleLiftedProbeFunctor (X : (operad A).Algebra) :
    strictRawModuleLiftedProbeCategory A X ⥤ (strictRawModuleRelativeCategory A X).category :=
  ULiftHom.down.{u, u + 1, u + 1} (C := strictRawModuleProbeCategory A X) ⋙
    strictRawModuleProbeRelativeFunctor A X

/-- 概要：同じ probe の全通常鎖を指定半自由模型の実 dg 単体へ送る。
方針：元の閉零鎖を高次成分零の同じ dg 単体にする。
規約：HA Construction 1.3.1.9、全次元。使われ方：同じ三角比較の指定端点。 -/
def strictRawModuleLiftedProbeDGSource (X : (operad A).Algebra) :
    nerve (strictRawModuleLiftedProbeCategory A X) ⟶ strictModuleInfinity A X where
  app Δ := ↾fun s => closedNerveSimplex
    (s ⋙ ULiftHom.down.{u, u + 1, u + 1} (C := strictRawModuleProbeCategory A X))
  naturality _ _ f := by
    ext s
    exact SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveSimplex_pullback
      (A := A) (D := SemifreeDGModules A (dgAlgebraCategory A ((assocForget A).obj X)))
      (s ⋙ ULiftHom.down.{u, u + 1, u + 1} (C := strictRawModuleProbeCategory A X))
      f.unop.toOrderHom

/-- 概要：同じ probe の全通常鎖の包含は元の全加群 dg 源と厳密に可換。
方針：既存の閉零鎖の dg 関手自然性を各次数に適用する。
規約：HA Construction 1.3.1.9、全関手の等式。使われ方：同じ retract の前合成。 -/
lemma strictRawModuleLiftedProbeDGSource_inclusion (X : (operad A).Algebra) :
    nerveMap (strictRawModuleLiftedProbeFunctor A X) ≫ strictRawModuleDGSource A X =
      strictRawModuleLiftedProbeDGSource A X ≫
        DifferentialGradedCategories.Functor.map
          (semifreeInclusion A (dgAlgebraCategory A ((assocForget A).obj X))) := by
  apply NatTrans.ext
  funext Δ
  apply ConcreteCategory.hom_ext
  intro s
  change closedNerveSimplex
      ((s ⋙ strictRawModuleLiftedProbeFunctor A X) ⋙
        ULiftHom.down.{u, u + 1, u + 1} (C := strictRawModuleCategory A X)) =
    (closedNerveSimplex
      (s ⋙ ULiftHom.down.{u, u + 1, u + 1} (C := strictRawModuleProbeCategory A X))).map
        (semifreeInclusion A (dgAlgebraCategory A ((assocForget A).obj X)))
  rw [dgFunctor_closedNerveSimplex]
  rfl

/-- 概要：元の全通常源を probe へ制限すると同じ指定半自由鎖と全関手同型。
方針：同じ解像度 retract を元の全鎖で前合成し、同じ厳密等式で移送する。
規約：HA §1.3.1、同じ可逆二胞体。使われ方：K の三角成分の全族。 -/
def strictRawModuleLiftedProbeSourceIso (X : (operad A).Algebra) :
    FunctorIso
      (nerveMap (strictRawModuleLiftedProbeFunctor A X) ≫ strictRawModuleSource A X)
      (strictRawModuleLiftedProbeDGSource A X) := by
  let D := dgAlgebraCategory A ((assocForget A).obj X)
  let e := (dgModuleResolutionRetractIso A D).precomp (strictRawModuleLiftedProbeDGSource A X)
  refine functorIsoTransport e ?_ (Category.comp_id _)
  calc
    _ = (strictRawModuleLiftedProbeDGSource A X ≫
          DifferentialGradedCategories.Functor.map (semifreeInclusion A D)) ≫ moduleResolution A D :=
      (Category.assoc _ _ _).symm
    _ = (nerveMap (strictRawModuleLiftedProbeFunctor A X) ≫ strictRawModuleDGSource A X) ≫
          moduleResolution A D :=
      congrArg (fun f => f ≫ moduleResolution A D)
        (strictRawModuleLiftedProbeDGSource_inclusion A X).symm
    _ = _ := Category.assoc _ _ _

/-- 概要：同じ K の全 probe 通常 nerve 上の三角比較は指定半自由鎖へ接続する。
方針：元の局所化三角を前合成し、同じ retract 比較を合成する。
規約：HA §1.3.4、同じ K と同じ全成分。使われ方：全 Hom 誘導射の照合。 -/
def strictRawModuleLiftedProbeComparisonIso (X : (operad A).Algebra) :
    FunctorIso
      (nerveMap (strictRawModuleLiftedProbeFunctor A X) ≫
        (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerveSourceMap (strictRawModuleRelativeCategory A X) ≫
          strictRawModuleComparison A X))
      (strictRawModuleLiftedProbeDGSource A X) :=
  (strictRawModuleComparison_sourceIso A X).precomp
    (nerveMap (strictRawModuleLiftedProbeFunctor A X)) ≪≫ strictRawModuleLiftedProbeSourceIso A X

end SerrePositivity.EInfinity.BarrattEccles
