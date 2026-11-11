module
public import SerrePositivity.KST.SConstruction.DGPerfectRealizationYonedaRestriction
public import SerrePositivity.KST.SConstruction.DGIdentityHomGluingStrictCone
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConePostcompArrow
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConeArrowComp
public import SerrePositivity.DifferentialGraded.Functor.DGFunctorClosedNaturality

/-!
概要：元小模型の二つの Yoneda 評価同型を元厳密比較の全 square に保持する。
方針：元代表評価の全 Hom 自然性を同じ元閉比較射へ適用する。
規約：元二軸・元比較・同じ評価成分を保持する。
使われ方：元実 gluing cone と実 realization 後の cone の全図式比較。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (E : Type v) [DGCategory R E] [Small.{u} E]
  (C : Type (max (u + 1) v)) [DGCategory R C] [Small.{u} C]
  (J : DGFunctor R C (PerfectDGModule R E))
  {P : Type (max (u + 1) v)} [DGCategory R P] (F G : DGFunctor R P C)
  (a : ∀ x, ForgetEnrichment.of (Complex R) (F.obj x) ⟶
    ForgetEnrichment.of (Complex R) (G.obj x))
  (h : ∀ x y, F.map x y ≫
      eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) (F.obj x)) (a y) =
      G.map x y ≫ eHomWhiskerRight (Complex R) (a x)
        (ForgetEnrichment.of (Complex R) (G.obj y)))
local notation "Y" => dgYoneda R C
local notation "V" => dgPerfectRealization R C E J
local notation "K" => dgPerfectModuleUnderlying R E J
local notation "F0" => DGFunctor.comp (F.comp (Y)) (V)
local notation "G0" => DGFunctor.comp (G.comp (Y)) (V)
local notation "F1" => DGFunctor.comp F (K)
local notation "G1" => DGFunctor.comp G (K)
local notation "ηY" => dgIdentityHomGluingYonedaStrictComparison R C F G a h
local notation "η0" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPostcomp (ηY) (V)
local notation "εF" => dgPerfectRealizationYonedaRestrictedStrictComparison R E C J F
local notation "εG" => dgPerfectRealizationYonedaRestrictedStrictComparison R E C J G

/-- 概要：元比較の同じ実 perfect 像を全厳密比較に束ねる。
方針：元閉比較の後合成全自然性を既存厳密構成子へ渡す。
規約：元実像射を保持。使われ方：全評価 square の終辺。 -/
def dgIdentityHomGluingRealizedModuleComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans (F1) (G1) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleStrictNatTransOfHomNaturality R E (F := (F1)) (G := (G1))
    (fun x => (K).onClosed.map (a x))
    (dgClosedComparison_postcomp_naturality R F G (K) a h)
local notation "η1" => dgIdentityHomGluingRealizedModuleComparison R E C J F G a h

/-- 概要：元実 perfect 像の全比較の閉射は元閉比較の同じ実像。
方針：元閉射・閉元対応の逆律を使う。
規約：元実射の厳密等式。使われ方：元評価 square の四境界照合。 -/
lemma dgIdentityHomGluingRealizedModuleComparison_arrow (x : P) :
    dgModuleNaturalConeArrow R E (F1) (G1) (η1) x = (K).onClosed.map (a x) := by
  change (closedHomEquiv R (RightModule R E) _ _).symm
    ((closedHomEquiv R (RightModule R E) _ _) ((K).onClosed.map (a x))) = _
  exact (closedHomEquiv R (RightModule R E) _ _).symm_apply_apply _

/-- 概要：元二軸の評価同型は同じ元比較と全厳密に可換。
方針：元全評価自然性を元閉射へ制限し全閉成分の外延性を使う。
規約：元全比較の等号。使われ方：元 gluing cone の全 square 比較。 -/
lemma dgIdentityHomGluingRealizedModuleSquare :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransComp (η0) (εG) = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransComp (εF) (η1) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTrans_ext
  intro x
  apply (closedHomEquiv R (RightModule R E) ((F0).obj x) ((G1).obj x)).symm.injective
  change dgModuleNaturalConeArrow R E (F0) (G1) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransComp (η0) (εG)) x =
    dgModuleNaturalConeArrow R E (F0) (G1) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransComp (εF) (η1)) x
  rw [dgModuleNaturalConeArrow_comp, dgModuleNaturalConeArrow_comp,
    dgPerfectRealizationYonedaRestrictedStrictComparison_arrow,
    dgPerfectRealizationYonedaRestrictedStrictComparison_arrow,
    dgIdentityHomGluingRealizedModuleComparison_arrow, dgModuleNaturalConePostcompArrow,
    dgIdentityHomGluingYonedaStrictComparison_arrow]
  exact dgFunctorClosedComparison_naturality R ((Y).comp (V)) (K)
    (dgPerfectRealizationYonedaMap R E C J)
    (dgPerfectRealizationYonedaMap_naturality R E C J) (a x)
end SerrePositivity.KST.SConstruction
