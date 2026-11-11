module
public import SerrePositivity.KST.SConstruction.DGPerfectRealizationYonedaNative
public import SerrePositivity.KST.SConstruction.DGModuleNaturalCone

/-!
概要：元小模型の代表評価全比較を同じ元入力関手へ制限する。
方針：元評価成分と元全 Hom 自然性をそのまま指定入力の Hom 作用へ適用する。
規約：関手等号による成分輸送を挟まず元評価射を保持する。
使われ方：元 gluing の左右の Yoneda 評価同型を保つ全 cone square 比較。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (E : Type v) [DGCategory R E] [Small.{u} E]
  (C : Type (max (u + 1) v)) [DGCategory R C] [Small.{u} C]
  (J : DGFunctor R C (PerfectDGModule R E))
  {P : Type (max (u + 1) v)} [DGCategory R P] (F : DGFunctor R P C)
local notation "V" => dgPerfectRealization R C E J
local notation "A" => DGFunctor.comp (F.comp (dgYoneda R C)) (V)
local notation "B" => DGFunctor.comp F (dgPerfectModuleUnderlying R E J)
local notation "ε" => dgPerfectRealizationYonedaStrictComparison R E C J

/-- 概要：同じ元代表評価全比較の元入力関手への制限。
方針：元評価成分を同じ実対象で評価する。
規約：元全 Hom を保持。使われ方：実 gluing の二軸の全評価比較。 -/
def dgPerfectRealizationYonedaRestrictedStrictComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans (A) (B) where
  app x := (ε).app (F.obj x)
  naturality z := (ε).naturality ((F.map _ _).f _ z)

/-- 概要：制限した全評価比較の cycle は元指定評価射の cycle。
方針：元代表評価全比較の同じ成分回収を使う。
規約：元実成分を変更しない。使われ方：native 全比較の指定閉射回収。 -/
lemma dgPerfectRealizationYonedaRestrictedStrictComparison_cycle (x : P) :
    (dgPerfectRealizationYonedaRestrictedStrictComparison R E C J F).app x =
      cycleFromUnit _ (ForgetEnrichment.homTo (Complex R)
        (dgPerfectRealizationYonedaMap R E C J (F.obj x))) := by
  exact dgPerfectRealizationYonedaStrictComparison_cycle R E C J (F.obj x)

/-- 概要：元制限全評価比較の閉射は同じ指定代表評価射。
方針：元 cycle 回収と閉射・閉元対応の逆律を使う。
規約：元評価射の厳密等式。使われ方：全 gluing cone square の閉成分。 -/
lemma dgPerfectRealizationYonedaRestrictedStrictComparison_arrow (x : P) :
    dgModuleNaturalConeArrow R E (A) (B)
      (dgPerfectRealizationYonedaRestrictedStrictComparison R E C J F) x =
        dgPerfectRealizationYonedaMap R E C J (F.obj x) := by
  apply (closedHomEquiv R (RightModule R E) _ _).injective
  apply Subtype.ext
  exact (dgModuleNaturalConeArrow_cycle R E (A) (B)
    (dgPerfectRealizationYonedaRestrictedStrictComparison R E C J F) x).trans
      (congrArg Subtype.val
        (dgPerfectRealizationYonedaRestrictedStrictComparison_cycle R E C J F x))

/-- 概要：元入力上の同じ代表評価を保持する native 全関手同型。
方針：元制限全厳密比較と同じ評価同型の可逆性を使用する。
規約：元評価全ホモトピーを保持。
使われ方：元 gluing の左右の全評価同型を保つ実 cone 比較。 -/
def dgPerfectRealizationYonedaRestrictedNerveComparison :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (A)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (B)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorIsoOfStrictNatTrans R E (F := (A)) (G := (B))
    (dgPerfectRealizationYonedaRestrictedStrictComparison R E C J F)
    (fun x => dgPerfectRealizationYonedaMap R E C J (F.obj x))
    (dgPerfectRealizationYonedaRestrictedStrictComparison_cycle R E C J F)
    (fun x => (dgPerfectRealizationRepresentableIso R C E J (F.obj x)).isIso_hom)
end SerrePositivity.KST.SConstruction
