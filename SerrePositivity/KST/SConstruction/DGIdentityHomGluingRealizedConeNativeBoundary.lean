module
public import SerrePositivity.KST.SConstruction.DGIdentityHomGluingRealizedConeNative
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConeNativeBoundary

/-!
概要：元実 cone の realization 全比較が元右包含を同じ評価射付きで保持する。
方針：元 cone image の逆の包含回収と元評価 square の包含回収を合成する。
規約：元包含・元評価・元全比較を保持し、別の辺代表を選ばない。
使われ方：元上指定二単体を実二段 realization へ接続する。
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


local notation "η1" => dgIdentityHomGluingRealizedModuleComparison R E C J F G a h
local notation "CY" => dgIdentityHomGluingStrictConeFamily R C F G a h
local notation "CB" => dgIdentityHomGluingModuleConeFamily R C F G a h
local notation "CT" => dgModuleNaturalConeFunctor R E (F1) (G1) (η1)

/-- 概要：元実 cone 評価の全比較は元右包含の評価像と厳密に可換。
方針：同じ cone image 逆と同じ二軸評価 square の native 包含則を貼る。
規約：元全関手射の等号。使われ方：元指定上二単体の評価境界。 -/
lemma dgIdentityHomGluingRealizedStrictConeNerveComparison_inr :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R P (RightModule R E)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPostcomp (dgModuleNaturalConeInr R C (F.comp (Y))
          (G.comp (Y)) (ηY)) (V)) ≫
      (dgIdentityHomGluingRealizedStrictConeNerveComparison R E C J F G a h).hom =
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R P (RightModule R E) (εG) ≫
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R P (RightModule R E)
            (dgModuleNaturalConeInr R E (F1) (G1) (η1)) := by
  unfold dgIdentityHomGluingRealizedStrictConeNerveComparison
  rw [Iso.trans_hom, Iso.symm_hom, ← Category.assoc,
    dgModuleNaturalConeImageNerveComparison_inr_inv,
    dgModuleNaturalConeSquareNerveComparison_inr]
end SerrePositivity.KST.SConstruction
