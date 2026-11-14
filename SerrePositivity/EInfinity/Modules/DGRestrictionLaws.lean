module

public import SerrePositivity.KST.LocalizingInvariants.DGRestrictionCompositionStrict
public import SerrePositivity.KST.LocalizingInvariants.DGRestrictionIdentityStrict
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleStrictNatTransIso
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleResolvedComposition
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleResolvedRawFactor
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleResolutionRetract

/-!
# 出力解像度を持つ dg 制限の恒等・合成

概要：HA §4.2.3 の dg 制限の既存の全 Hom 自然な比較を、実出力解像度へ送る。
方針：既存の厳密自然変換と準同型を保つ制限を使う。
規約：制限が半自由性や射影性を保つとは仮定しない。
使われ方：BE 加群の同じ restriction の恒等・合成比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.Modules
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.KST.LocalizingInvariants
variable (A : Type u) [CommRing A]
variable (D E K : Type v) [DGCategory A D] [Small.{u} D]
  [DGCategory A E] [Small.{u} E] [DGCategory A K] [Small.{u} K]

/-- 概要：全 dg 加群上の制限の合成比較（HA §4.2.3）。
方針：既存の全次数自然な加群同型を実 nerve へ送る。
規約：同じ graphRestrictionCompositionIso の成分。使われ方：解像度付き合成。 -/
def restrictionCompRawIso (F : DGFunctor A D E) (G : DGFunctor A E K) :
    FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgModuleRestriction A E K G.op) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgModuleRestriction A D E F.op))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgModuleRestriction A D K (F.comp G).op)) := by
  have e := dgModuleFunctorIsoOfStrictNatTrans A D
    (dgRestrictionCompositionStrict A D E K F G)
    (fun M => (graphRestrictionCompositionIso A D E K F G).hom.app
      (ForgetEnrichment.of (Complex A) M)) (fun _ => rfl) (fun _ => inferInstance)
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp] using e

/-- 概要：全 dg 加群上の恒等制限比較（HA §4.2.3）。
方針：既存の逆単位比較を実 nerve へ送り逆を取る。
規約：元の恒等制限同型を保持。使われ方：解像度付き恒等比較。 -/
def restrictionIdRawIso :
    FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgModuleRestriction A D D (DGFunctor.id D).op))
      (𝟙 (dgModuleNerve A D)) := by
  have e := dgModuleFunctorIsoOfStrictNatTrans A D
    (dgRestrictionIdentityInvStrict A D)
    (fun M => (moduleRestrictionIdObjIso A D (ForgetEnrichment.of (Complex A) M)).inv)
    (fun _ => rfl) (fun _ => inferInstance)
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_id] using e.symm

/-- 概要：制限の出力を全関手的に解像する（HA §4.2.3）。
方針：半自由加群の全包含の後の制限に実出力解像度を適用。
規約：制限の射影性保存は不要。使われ方：変わる底の native restriction。 -/
def resolvedRestriction (F : DGFunctor A D E) :
    dgModuleDerivedInfinityCategory A E ⟶ dgModuleDerivedInfinityCategory A D :=
  dgModuleResolvedInfinity A _ D
    ((dgFullSubcategoryInclusion A (RightModule A E) (dgModuleSemifreeProperty A E)).comp
      (dgModuleRestriction A D E F.op))

/-- 概要：同じ解像度付き制限の合成比較（HA §4.2.3）。
方針：制限が解像度の増大の準同型を保つことと、実出力合成の比較を使う。
規約：全関手同型。使われ方：BE の全辺に対する反変性。 -/
def resolvedRestriction_compIso (F : DGFunctor A D E) (G : DGFunctor A E K) :
    FunctorIso (resolvedRestriction A E K G ≫ resolvedRestriction A D E F)
      (resolvedRestriction A D K (F.comp G)) := by
  let I := dgFullSubcategoryInclusion A (RightModule A K) (dgModuleSemifreeProperty A K)
  let RG := dgModuleRestriction A E K G.op
  let RF := dgModuleRestriction A D E F.op
  let RGF := dgModuleRestriction A D K (F.comp G).op
  have e := dgModuleResolvedInfinity_compositionIso A (SemifreeDGModules A K) E D
    (I.comp RG) RF (fun X => by
      rw [dgModuleRestriction_map]
      exact moduleRestriction_quasiIso A D E F.op X.augmentation X.quasiIso)
  have raw : FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map ((I.comp RG).comp RF)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (I.comp RGF)) := by
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp, Category.assoc] using
      (restrictionCompRawIso A D E K F G).precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map I)
  exact e ≪≫ dgModuleResolvedInfinity_isoOfRawFunctorIso A (SemifreeDGModules A K) D
    ((I.comp RG).comp RF) (I.comp RGF) raw

/-- 概要：同じ解像度付き制限の恒等比較（HA §4.2.3）。
方針：生の恒等比較の後に、同じ半自由包含の解像度の retract 比較を使う。
規約：全関手同型。使われ方：BE 加群族の単位法則。 -/
def resolvedRestriction_idIso :
    FunctorIso (resolvedRestriction A D D (DGFunctor.id D))
      (𝟙 (dgModuleDerivedInfinityCategory A D)) := by
  let I := dgFullSubcategoryInclusion A (RightModule A D) (dgModuleSemifreeProperty A D)
  let R := dgModuleRestriction A D D (DGFunctor.id D).op
  let Q := dgModuleResolvedInfinity A (RightModule A D) D (DGFunctor.id (RightModule A D))
  have e : FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (I.comp R) ≫ Q) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map I ≫ Q) := by
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp, Category.assoc, Category.comp_id] using
      ((restrictionIdRawIso A D).precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map I)).postcomp Q
  exact dgModuleResolvedInfinity_rawFactorIso A (SemifreeDGModules A D) D (I.comp R) ≪≫
    e ≪≫ dgModuleResolutionRetractIso A D

end SerrePositivity.EInfinity.Modules
