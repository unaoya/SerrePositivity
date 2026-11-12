module
public import SerrePositivity.KST.SConstruction.DGPerfectComparisonInverseRotationRealized
public import SerrePositivity.KST.SConstruction.DGIdentityHomGluingInverseRotationRealizedBoundary

/-!
概要：同じ二段実逆回転全比較に元包含・元評価・負符号付き長辺を保持する。
方針：元包含の全可換式を第二段実評価で後合成し、同じ代表評価を合成する。
規約：元全比較を別の同型で置換しない。
使われ方：同じ resolved 射影の固定 ν 全比較への境界接続。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories MonoidalCategory

private lemma normalizeComposite
    {A X : SSet.{u}} {f g f' g' z z' : A ⟶ X}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso g' z)
    (hs : f = f') (ht : g = g') (hz : z = z') :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq e hs ht).trans t) rfl hz) hs.symm rfl =
        e.trans (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq t ht.symm hz) := by
  cases hs
  cases ht
  cases hz
  rfl

private lemma postcompInclusion
    {A X Y : SSet.{u}} [SSet.Quasicategory X] [SSet.Quasicategory Y]
    {f0 f1 f2 f3 : A ⟶ X} {g3 : A ⟶ Y}
    (a : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom f0 f1) (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f1 f3) (b : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f0 f2)
    (c : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom f2 f3) (q : X ⟶ Y) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (f3 ≫ q) g3)
    (hc : a ≫ e.hom = b.hom ≫ c) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp f0 f1 q a ≫ ((e.postcomp q).trans t).hom =
      (b.postcomp q).hom ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp f2 f3 q c ≫ t.hom) := by
  have hs := congrArg (fun m => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp f0 f3 q m) hc
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp_comp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp_comp] at hs
  rw [Iso.trans_hom, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_postcomp_hom_typed,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_postcomp_hom_typed, ← Category.assoc, hs, Category.assoc]

variable (R : Type u) [CommRing R] (E : Type v) [DGCategory R E] [Small.{u} E]
  {P : Type (max (u + 1) v)} [DGCategory R P] [Small.{u} P]
  (F G : DGFunctor R P (PerfectDGModule R E))
  (τ : DGFunctorParamTrans R P (PerfectDGModule R E) (𝟙_ (Complex R)) F G)
local notation "T" => DGPerfectComparisonBase R E F G
local notation "family" => dgPerfectComparisonFamily R E F G
local notation "J" => dgSmallPerfectEnvelopeInclusion R E (P ⊕ P) (family)
local notation "V" => dgPerfectRealization R (T) E (J)
local notation "F0" => dgPerfectComparisonFirst R E F G
local notation "G0" => dgPerfectComparisonSecond R E F G
local notation "a" => dgPerfectComparisonMap R E F G τ
local notation "h" => dgPerfectComparisonMap_hom_naturality R E F G τ
local notation "H" => dgPerfectComparisonHomGluingFunctor R E F G τ
local notation "Q" => dgIdentityInverseRotationRealizedConeFamily R (T)

local notation "TF" => dgIdentityHomGluingInverseRotationTargetFamily R (T) (F0) (G0) (a) (h)
local notation "RF" => DGFunctor.comp (H) (Q)
local notation "GY" => DGFunctor.comp (G0) (dgYoneda R (T))
local notation "FS" => DGFunctor.comp (DGFunctor.comp (F0) (dgYoneda R (T))) (moduleShiftDG R (T) 1)
local notation "S" => moduleShiftDG R (T) (-1)
local notation "FSS" => DGFunctor.comp (FS) (S)
local notation "η" => dgIdentityHomGluingYonedaStrictComparison R (T) (F0) (G0) (a) (h)
local notation "δs" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPostcomp
  (dgModuleNaturalConeConnecting R (T) (DGFunctor.comp (F0) (dgYoneda R (T)))
    (DGFunctor.comp (G0) (dgYoneda R (T))) (η)) (S)
local notation "AS" => DGFunctor.comp
  (dgIdentityHomGluingStrictConeFamily R (T) (F0) (G0) (a) (h)) (S)
local notation "LONG" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransComp
  (dgModuleNaturalConeInr R (T) (AS) (FSS) (δs))
  (dgModuleNaturalInverseRotation R (T) (DGFunctor.comp (F0) (dgYoneda R (T)))
    (DGFunctor.comp (G0) (dgYoneda R (T))) (η))
local notation "e" => dgIdentityHomGluingInverseRotationRealizedNerveComparison
  R (T) (F0) (G0) (a) (h)
local notation "b" => dgIdentityHomGluingInverseRotationTargetNerveComparison
  R (T) (F0) (G0) (a) (h)
local notation "inr" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R P (RightModule R (T))
  (dgIdentityHomGluingInverseRotationRealizedInr R (T) (F0) (G0) (a) (h))
local notation "long" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R P (RightModule R (T)) (LONG)
local notation "eY" => dgPerfectRealizationYonedaRestrictedNerveComparison R E (T) (J) (G0)

/-- 概要：元第二実像の全包含回収は元第二 Perf 関手そのもの。
方針：元指定像小模型の全包含則を使う。
規約：全 dg 関手の等号。使われ方：二段全比較の元終端照合。 -/
lemma dgPerfectComparisonSecondRealizationTarget :
    (G0).comp (dgPerfectModuleUnderlying R E (J)) = dgPerfectModuleUnderlying R E G :=
  dgPerfectModuleUnderlying_comp_of_eq R E (G0) (J) G
    (dgSmallPerfectEnvelopeFunctorLift_inclusion R E (P ⊕ P) (family) G Sum.inr (fun _ => rfl))

/-- 概要：二段全比較の終端の同じ指定代表評価。
方針：元代表評価の端点を同じ native 後合成表示へ移す。
規約：元全評価同型を保持。使われ方：負符号付き長辺の終端比較。 -/
def dgPerfectComparisonInverseRotationFinalEvaluation :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (GY) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (V))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgPerfectModuleUnderlying R E G)) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (eY) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp (GY) (V))
    (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgPerfectComparisonSecondRealizationTarget R E F G))

/-- 概要：二段全比較は元全逆回転と同じ指定代表評価の合成そのもの。
方針：抽象的な端点移送の合成則を元構成へ適用する。
規約：同じ全比較の等号。使われ方：元包含境界を既存二段全比較へ接続。 -/
lemma dgPerfectComparisonInverseRotationRealizedNerveComparison_composite :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (dgPerfectComparisonInverseRotationRealizedNerveComparison R E F G τ)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp (RF) (V)) rfl =
      ((e).postcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (V))).trans
        (dgPerfectComparisonInverseRotationFinalEvaluation R E F G) := by
  exact normalizeComposite ((e).postcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (V))) (eY)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp (RF) (V)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp (GY) (V)).symm
    (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgPerfectComparisonSecondRealizationTarget R E F G))

/-- 概要：元包含と同じ二段全比較の合成は元負符号付き長辺と同じ終端評価。
方針：元全包含 square を第二段実評価へ送り、同じ元終端を合成する。
規約：元実始域・元包含・全関手同型を保持。
使われ方：固定 ν の上指定二単体の三辺同時接続。 -/
lemma dgPerfectComparisonInverseRotationRealizedNerveComparison_inr :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (TF)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (RF)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (V)) (inr) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (dgPerfectComparisonInverseRotationRealizedNerveComparison R E F G τ)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp (RF) (V)) rfl).hom =
      ((b).postcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (V))).hom ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (FSS)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (GY)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (V)) (long) ≫
          (dgPerfectComparisonInverseRotationFinalEvaluation R E F G).hom) := by
  rw [dgPerfectComparisonInverseRotationRealizedNerveComparison_composite]
  exact postcompInclusion (inr) (e) (b) (long) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (V))
    (dgPerfectComparisonInverseRotationFinalEvaluation R E F G)
    (dgIdentityHomGluingInverseRotationRealizedNerveComparison_inr R (T) (F0) (G0) (a) (h))
end SerrePositivity.KST.SConstruction
