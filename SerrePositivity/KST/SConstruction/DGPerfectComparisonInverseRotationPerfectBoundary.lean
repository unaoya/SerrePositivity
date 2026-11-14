module
public import SerrePositivity.KST.SConstruction.DGPerfectComparisonInverseRotationPerfectInclusion
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.SimplicialFunctors.FunctorHomEndpointTransport

/-!
概要：元二段全比較の負符号付き包含境界を同じ実 Perf 全関手間へ反映する。
方針：元長辺の全合成を充満忠実な Perf 包含から戻し、元全包含式を反映する。
規約：元全比較・元実包含・元負符号付き長辺を保持する。
使われ方：同じ resolved 射影への固定 ν の上指定二単体の境界接続。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories MonoidalCategory

private lemma normalizeBoundary
    {A X : SSet.{u}} [SSet.Quasicategory X]
    {f0 f1 f2 g0 g1 g2 : A ⟶ X}
    (a : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom f0 f1) (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f1 f2)
    (b : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom g0 g1) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso g1 g2) (r : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom g0 g2)
    (h0 : f0 = g0) (h1 : f1 = g1) (h2 : f2 = g2)
    (ha : HEq a b) (he : HEq e t) (hr : b ≫ t.hom = r) :
    a ≫ e.hom = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomOfMapEq r h0.symm h2.symm := by
  subst g0 g1 g2
  cases eq_of_heq ha
  cases eq_of_heq he
  exact hr

private lemma reflectCompositeBoundary
    {A X Y : SSet.{u}} [SSet.Quasicategory X] [SSet.Quasicategory Y]
    {i : X ⟶ Y} (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful i) {f0 f1 f2 : A ⟶ X}
    (a : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom f0 f1) (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f1 f2) (b : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom f0 f2)
    (em : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (f1 ≫ i) (f2 ≫ i)) (bm : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (f0 ≫ i) (f2 ≫ i))
    (he : e.postcomp i = em) (hb : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp f0 f2 i b = bm)
    (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp f0 f1 i a ≫ em.hom = bm) : a ≫ e.hom = b := by
  apply (hi.postcompose A).toHoFullyFaithful.map_injective
  change _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp f0 f2 i (a ≫ e.hom) = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp f0 f2 i b
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp_comp, ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_postcomp_hom_typed, he, hb]
  exact h

private lemma moduleInrPostcompBridge
    (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [DGCategory R C] [Small.{u} C]
    (E : Type v) [DGCategory R E] [Small.{u} E]
    {P : Type (max (u + 1) v)} [DGCategory R P]
    {A B : DGFunctor R P (RightModule R C)} (η : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans A B)
    (V : DGFunctor R (RightModule R C) (RightModule R E))
    (F G : DGFunctor R P (PerfectDGModule R E))
    (a : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map G))
    (ha : HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map G)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (perfectDGModuleInclusion R E Set.univ)) a)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R P (RightModule R E) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPostcomp η V))) :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map G)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (perfectDGModuleInclusion R E Set.univ)) a)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map A) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map B) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map V)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R P (RightModule R C) η)) :=
  ha.trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom_postcomp_heq R P
    (RightModule R C) (RightModule R E) η V)

/-- 概要：元 Perf 関手の包含後の nerve は同じ元加群値表示を回収する。
方針：元全包含の等号と nerve の全合成則を使用する。
規約：全単体の等号。使われ方：元全境界の Perf 反映における端点照合。 -/
lemma dgPerfectFunctorUnderlyingNerve (R : Type u) [CommRing R]
    (E : Type v) [DGCategory R E] [Small.{u} E]
    {P : Type (max (u + 1) v)} [DGCategory R P]
    (F : DGFunctor R P (PerfectDGModule R E)) (G : DGFunctor R P (RightModule R E))
    (h : dgPerfectModuleUnderlying R E F = G) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (perfectDGModuleInclusion R E Set.univ) = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map G :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp F _).symm.trans
    (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map ((dgPerfectModuleUnderlying_inclusion R E F).symm.trans h))

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

local notation "TPF" => dgPerfectComparisonInverseRotationPerfectTargetFamily R E F G τ
local notation "RP" => dgPerfectComparisonInverseRotationPerfectRealizedFamily R E F G τ
local notation "i" => perfectDGModuleInclusion R E Set.univ
local notation "IP" => dgPerfectComparisonInverseRotationPerfectInr R E F G τ
local notation "EP" => dgPerfectComparisonInverseRotationPerfectNerveComparison R E F G τ
local notation "EM" => dgPerfectComparisonInverseRotationPerfectModuleComparison R E F G τ
local notation "ER" => _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq
  (dgPerfectComparisonInverseRotationRealizedNerveComparison R E F G τ)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp (RF) (V)) rfl
local notation "IR" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPostcomp
  (dgIdentityHomGluingInverseRotationRealizedInr R (T) (F0) (G0) (a) (h)) (V)
local notation "s0" => Eq.trans
  (dgPerfectFunctorUnderlyingNerve R E (TPF) _
    (dgPerfectComparisonInverseRotationPerfectTargetFamily_underlying R E F G τ))
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp (TF) (V))
local notation "s1" => Eq.trans
  (dgPerfectFunctorUnderlyingNerve R E (RP) _
    (dgPerfectComparisonInverseRotationPerfectRealizedFamily_underlying R E F G τ))
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp (RF) (V))
local notation "s2" => dgPerfectFunctorUnderlyingNerve R E G
  (dgPerfectModuleUnderlying R E G) rfl

/-- 概要：元評価包含の終端を、元負符号付き長辺と同じ全代表評価で表す。
方針：元右軸全評価・元長辺・元第二段終端評価を合成する。
規約：元負符号と全自然性を保持。使われ方：Perf 内へ戻す元全境界。 -/
def dgPerfectComparisonInverseRotationSignedBoundary :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (TF) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (V))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgPerfectModuleUnderlying R E G)) :=
  ((b).postcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (V))).hom ≫
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (FSS)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (GY)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (V)) (long) ≫
      (dgPerfectComparisonInverseRotationFinalEvaluation R E F G).hom)

/-- 概要：同じ元全負符号付き境界を Perf 全包含の両端に正規化する。
方針：同じ元実像回収の等号で端点だけを移す。
規約：元全射を保持。使われ方：充満忠実包含による逆像。 -/
def dgPerfectComparisonInverseRotationSignedModuleBoundary :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (TPF) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (i)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map G ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (i)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomOfMapEq (dgPerfectComparisonInverseRotationSignedBoundary R E F G τ)
    (s0).symm (s2).symm

private lemma moduleInrRaw :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (TPF)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (RP)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (i))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R P (PerfectDGModule R E) (IP)))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (TF)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (RF)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (V)) (inr)) :=
  moduleInrPostcompBridge R (T) E
    (dgIdentityHomGluingInverseRotationRealizedInr R (T) (F0) (G0) (a) (h)) (V)
    (TPF) (RP) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R P (PerfectDGModule R E) (IP))
    (dgPerfectComparisonInverseRotationPerfectInr_nerve_inclusion R E F G τ)

private lemma moduleComparisonRaw : HEq (EM) (ER) :=
  (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq_heq _ _ _).trans (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq_heq _ _ _).symm

/-- 概要：元二段実包含と同じ元全比較の合成は正規化した負符号付き境界。
方針：元全射回収・同じ全同型の端点移送と元包含式を照合する。
規約：全関手射の等号。使われ方：Perf 内の元包含則の反映。 -/
lemma dgPerfectComparisonInverseRotationModuleBoundary_inr :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (TPF)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (RP)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (i))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R P (PerfectDGModule R E) (IP)) ≫ (EM).hom =
        dgPerfectComparisonInverseRotationSignedModuleBoundary R E F G τ := by
  exact normalizeBoundary
    (f0 := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (TPF) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (i))
    (f1 := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (RP) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (i))
    (f2 := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map G ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (i))
    (g0 := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (TF) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (V))
    (g1 := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (RF) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (V))
    (g2 := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgPerfectModuleUnderlying R E G))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (TPF)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (RP)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (i))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R P (PerfectDGModule R E) (IP))) (EM)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (TF)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (RF)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (V)) (inr)) (ER)
    (dgPerfectComparisonInverseRotationSignedBoundary R E F G τ)
    (s0) (s1) (s2) (moduleInrRaw R E F G τ) (moduleComparisonRaw R E F G τ)
    (dgPerfectComparisonInverseRotationRealizedNerveComparison_inr R E F G τ)

local notation "ff" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFullSubcategoryInclusionNerve_isFullyFaithful R (RightModule R E)
  (modulePerfectProjectiveOver R E Set.univ)

/-- 概要：元負符号付き全境界を同じ実 Perf 関手間に保持する。
方針：充満忠実な後合成の全射逆像を使用する。
規約：元全加群射の指定逆像。使われ方：固定 ν へ送る元長辺。 -/
def dgPerfectComparisonInverseRotationSignedPerfectBoundary :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (TPF)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map G) :=
  ((ff).postcompose (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R P)).toHoFullyFaithful.preimage
    (dgPerfectComparisonInverseRotationSignedModuleBoundary R E F G τ)

/-- 概要：同じ元負符号付き Perf 境界は包含後に元全境界を厳密回収する。
方針：充満忠実包含による全射逆像の回収則を使う。
規約：全関手射の等号。使われ方：元二単体の包含境界の接続。 -/
lemma dgPerfectComparisonInverseRotationSignedPerfectBoundary_inclusion :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (TPF)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map G) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (i))
      (dgPerfectComparisonInverseRotationSignedPerfectBoundary R E F G τ) =
        dgPerfectComparisonInverseRotationSignedModuleBoundary R E F G τ :=
  ((ff).postcompose (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R P)).toHoFullyFaithful.map_preimage
    (X := SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (TPF))))
    (Y := SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map G))) _

/-- 概要：同じ実 Perf 全比較も元包含を同じ元負符号付き全境界へ運ぶ。
方針：全包含後の元等式を充満忠実性で反映する。
規約：元実包含・元全比較を変更しない。使われ方：固定 ν 上指定二単体の境界。 -/
lemma dgPerfectComparisonInverseRotationPerfectNerveComparison_inr :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R P (PerfectDGModule R E) (IP) ≫ (EP).hom =
      dgPerfectComparisonInverseRotationSignedPerfectBoundary R E F G τ :=
  reflectCompositeBoundary (ff)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R P (PerfectDGModule R E) (IP)) (EP)
    (dgPerfectComparisonInverseRotationSignedPerfectBoundary R E F G τ) (EM)
    (dgPerfectComparisonInverseRotationSignedModuleBoundary R E F G τ)
    (dgPerfectComparisonInverseRotationPerfectNerveComparison_postcomp R E F G τ)
    (dgPerfectComparisonInverseRotationSignedPerfectBoundary_inclusion R E F G τ)
    (dgPerfectComparisonInverseRotationModuleBoundary_inr R E F G τ)
end SerrePositivity.KST.SConstruction
