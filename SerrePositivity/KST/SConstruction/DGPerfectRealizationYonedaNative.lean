module
public import SerrePositivity.KST.SConstruction.DGPerfectRealization
public import SerrePositivity.KST.SConstruction.DGPerfectModuleUnderlying
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Actions.DGModuleStrictNatTransIso

/-!
概要：元小模型の Yoneda 評価を同じ指定 realization の全比較に束ねる。
方針：元代表加群の右単位同型の全 Hom 自然性を既存構成子へ渡す。
規約：元代表評価同型の閉成分を保持する。
使われ方：元 gluing 全実逆回転比較から固定 ν の全比較への評価因子。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
private lemma factoryCycle {R : Type u} [CommRing R] {E : Type v}
    [DGCategory R E] [Small.{u} E]
    {P : Type (max (u + 1) v)} [DGCategory R P]
    (F G : DGFunctor R P (RightModule R E))
    (a : ∀ x, ForgetEnrichment.of (Complex R) (F.obj x) ⟶
      ForgetEnrichment.of (Complex R) (G.obj x))
    (h : ∀ x y, F.map x y ≫ moduleHomPostcompose R E _ _ _ (a y) =
      G.map x y ≫ moduleHomPrecompose R E _ _ _ (a x)) (x : P) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleStrictNatTransOfHomNaturality R E (F := F) (G := G) a h).app x =
      cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) (a x)) := rfl
variable (R : Type u) [CommRing R] (E : Type v) [DGCategory R E] [Small.{u} E]
  (C : Type (max (u + 1) v)) [DGCategory R C] [Small.{u} C]
  (F : DGFunctor R C (PerfectDGModule R E))
local notation "V" => dgPerfectRealization R C E F
local notation "A" => DGFunctor.comp (dgYoneda R C) (V)
local notation "B" => dgPerfectModuleUnderlying R E F

/-- 概要：同じ元代表評価同型の実閉射族。
方針：元 realization の指定代表同型の順射を保持する。
規約：元成分を変更しない。使われ方：Yoneda 評価の全厳密比較。 -/
def dgPerfectRealizationYonedaMap (x : C) :
    ForgetEnrichment.of (Complex R) ((A).obj x) ⟶
      ForgetEnrichment.of (Complex R) ((B).obj x) :=
  (dgPerfectRealizationRepresentableIso R C E F x).hom

/-- 概要：元評価同型の閉射族は元全 Hom 複体に自然。
方針：同じ元右単位同型の全自然性を関手合成の端点へ回収する。
規約：閉零次数に制限しない。使われ方：元全比較の厳密構成。 -/
lemma dgPerfectRealizationYonedaMap_naturality (x y : C) :
    (A).map x y ≫ moduleHomPostcompose R E _ _ _ (dgPerfectRealizationYonedaMap R E C F y) =
      (B).map x y ≫ moduleHomPrecompose R E _ _ _ (dgPerfectRealizationYonedaMap R E C F x) := by
  exact (Category.assoc _ _ _).trans (dgPerfectRealizationRepresentableIso_naturality R C E F x y)

/-- 概要：元 Yoneda 評価同型の同じ全厳密比較。
方針：元閉射族と全 Hom 自然性を既存の厳密構成子へ渡す。
規約：指定実成分を保持。使われ方：元 gluing 全比較の実 realization。 -/
def dgPerfectRealizationYonedaStrictComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans (A) (B) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleStrictNatTransOfHomNaturality R E
    (F := (A)) (G := (B)) (dgPerfectRealizationYonedaMap R E C F)
    (dgPerfectRealizationYonedaMap_naturality R E C F)

/-- 概要：全厳密評価比較の cycle は元指定評価射の cycle。
方針：同じ既存構成子の成分回収を適用する。
規約：元閉射を変更しない。使われ方：同じ native 全比較の構成。 -/
lemma dgPerfectRealizationYonedaStrictComparison_cycle (x : C) :
    (dgPerfectRealizationYonedaStrictComparison R E C F).app x =
      cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) (dgPerfectRealizationYonedaMap R E C F x)) := by
  exact factoryCycle (A) (B) (dgPerfectRealizationYonedaMap R E C F)
    (dgPerfectRealizationYonedaMap_naturality R E C F) x

/-- 概要：元小模型の Yoneda 評価を保つ同じ native 全関手同型。
方針：元全厳密比較・元 cycle 回収・同じ代表評価同型の可逆性を使う。
規約：点ごとの同値選択を使用しない。
使われ方：実逆回転比較を元実 perfect 像へ運ぶ評価因子。 -/
def dgPerfectRealizationYonedaNerveComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (A)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (B)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorIsoOfStrictNatTrans R E
    (F := (A)) (G := (B)) (dgPerfectRealizationYonedaStrictComparison R E C F)
    (dgPerfectRealizationYonedaMap R E C F)
    (dgPerfectRealizationYonedaStrictComparison_cycle R E C F)
    (fun x => (dgPerfectRealizationRepresentableIso R C E F x).isIso_hom)
end SerrePositivity.KST.SConstruction
