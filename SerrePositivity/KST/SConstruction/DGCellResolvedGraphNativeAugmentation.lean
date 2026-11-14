module
public import SerrePositivity.KST.SConstruction.DGCellResolvedGraphPerfectFunctor
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Resolutions.DGModuleResolutionStrictNatTransInvertible
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Actions.DGModuleStrictNatTrans

/-!
概要：同じ解像度 graph 増大を native 導来加群値の全関手同型として保持する。
方針：元 bimodule 増大の全 Hom 自然性と準同型性を実 nerve の変換へ送る。
規約：比較射の増大 square の coherence は別工程。導来射等号で代用しない。
使われ方：元 cell 始域の中央比較の二成分を全単体で回収する。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (B : Type (max (u + 1) v))
  [DGCategory R B] [Small.{u} B]
local notation "P" => DGCategoryCellResolution.Source R B

/-- 概要：元の同じ制限 graph を実加群値の全 dg 関手として読む。
方針：同じ bimodule の全左作用を保持する。規約：始域は元 cell 分解。
使われ方：実増大比較の終域。 -/
def dgCellRestrictedGraphModuleFunctor (F : DGFunctor R B B) :
    DGFunctor R (P) (RightModule R (P)) :=
  BimoduleCategory.underlying R (P) (P) (dgCellRestrictedGraph R B F)

/-- 概要：同じ graph 解像度増大の元閉零成分。
方針：同じ bimodule 増大を左対象で評価する。規約：元の射を保持。
使われ方：全自然な実 nerve 比較の成分。 -/
def dgCellResolvedGraphAugmentationMap (F : DGFunctor R B B) (x : P) :
    ForgetEnrichment.of (Complex R) ((dgCellResolvedGraphModuleFunctor R B F).obj x) ⟶
      ForgetEnrichment.of (Complex R) ((dgCellRestrictedGraphModuleFunctor R B F).obj x) :=
  (dgCellResolvedGraphResolution R B F).π.val x

/-- 概要：同じ増大の全 Hom 自然性。
方針：元 bimodule 射の指定自然性を読む。規約：全次数を保持。
使われ方：実厳密 dg 自然変換の構成。 -/
lemma dgCellResolvedGraphAugmentationMap_naturality (F : DGFunctor R B B) (x y : P) :
    (dgCellResolvedGraphModuleFunctor R B F).map x y ≫
        moduleHomPostcompose R (P) _ _ _ (dgCellResolvedGraphAugmentationMap R B F y) =
      (dgCellRestrictedGraphModuleFunctor R B F).map x y ≫
        moduleHomPrecompose R (P) _ _ _ (dgCellResolvedGraphAugmentationMap R B F x) :=
  (dgCellResolvedGraphResolution R B F).π.property x y

/-- 概要：同じ graph 増大の全厳密 dg 自然変換。
方針：元の全自然な閉零成分を実変換へ束ねる。規約：元射を保持。
使われ方：同じ全単体の native 増大比較。 -/
def dgCellResolvedGraphAugmentationStrictNatTrans (F : DGFunctor R B B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans (dgCellResolvedGraphModuleFunctor R B F)
      (dgCellRestrictedGraphModuleFunctor R B F) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleStrictNatTransOfHomNaturality R (P)
    (dgCellResolvedGraphAugmentationMap R B F)
    (dgCellResolvedGraphAugmentationMap_naturality R B F)

/-- 概要：同じ graph 増大の導来加群値の全関手射は可逆。
方針：元実増大の全点準同型性を同じ全自然変換に適用する。
規約：H⁰ の対象別同型だけを結論にしない。使われ方：元 native 成分の全回収。 -/
lemma dgCellResolvedGraphAugmentationNativeHom_isIso (F : DGFunctor R B B) :
    IsIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgCellResolvedGraphModuleFunctor R B F))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgCellRestrictedGraphModuleFunctor R B F))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R (RightModule R (P)) (P) (DGFunctor.id (RightModule R (P))))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R (P) (RightModule R (P))
        (dgCellResolvedGraphAugmentationStrictNatTrans R B F))) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolution_strictNatTrans_isIso_of_quasiIso R (P) (P)
    (dgCellResolvedGraphAugmentationMap R B F)
    (dgCellResolvedGraphAugmentationMap_naturality R B F)
    (dgCellResolvedGraph_evaluation_quasiIso R B F)

/-- 概要：同じ graph 増大の実導来加群値の全関手同型。
方針：指定した元増大の関手射をそのまま同型へ束ねる。
規約：始域・全単体・増大射を保持。使われ方：中央射の native 比較の二縦辺。 -/
def dgCellResolvedGraphAugmentationNativeComparison (F : DGFunctor R B B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgCellResolvedGraphModuleFunctor R B F) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R (RightModule R (P)) (P) (DGFunctor.id (RightModule R (P))))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgCellRestrictedGraphModuleFunctor R B F) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R (RightModule R (P)) (P) (DGFunctor.id (RightModule R (P)))) := by
  letI := dgCellResolvedGraphAugmentationNativeHom_isIso R B F
  exact asIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgCellResolvedGraphModuleFunctor R B F))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgCellRestrictedGraphModuleFunctor R B F))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R (RightModule R (P)) (P) (DGFunctor.id (RightModule R (P))))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R (P) (RightModule R (P))
      (dgCellResolvedGraphAugmentationStrictNatTrans R B F)))

end SerrePositivity.KST.SConstruction
