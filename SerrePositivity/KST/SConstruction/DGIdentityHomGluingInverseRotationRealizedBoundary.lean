module
public import SerrePositivity.KST.SConstruction.DGIdentityHomGluingInverseRotationRealizedNative
public import SerrePositivity.KST.SConstruction.DGIdentityHomGluingInverseRotationRestrictedInclusion
public import SerrePositivity.KST.SConstruction.DGIdentityHomGluingInverseRotationUpperActualBoundary
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.FunctorHomTypedWhiskerAlgebra

/-!
概要：元始域上の実逆回転全評価比較を元包含・負符号付き長辺へ接続する。
方針：元実全評価の包含 square を前合成し、同じ入力回収・指定逆全比較を合成する。
規約：元全比較・元包含・元長辺を選び直さず、検証上限を変更しない。
使われ方：二段 Perf 全比較と固定 ν 上指定二単体の接続。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories

private lemma precompInclusionEquation
    {A B X : SSet.{u}} [SSet.Quasicategory X]
    {f0 f1 f2 f3 : A ⟶ X} (a : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom f0 f1) (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f1 f3)
    (b : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f0 f2) (c : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom f2 f3)
    (he : a ≫ e.hom = b.hom ≫ c) (p : B ⟶ A) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp f0 f1 p a ≫ (e.precomp p).hom =
      (b.precomp p).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp f2 f3 p c := by
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp_comp f0 f1 f3 p a e.hom).symm.trans
    ((congrArg (fun t => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp f0 f3 p t) he).trans
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp_comp f0 f2 f3 p b.hom c))

private lemma recoverInclusionSquare
    {A X : SSet.{u}} [SSet.Quasicategory X]
    {f0 f1 f2 f3 g0 g1 g2 g3 : A ⟶ X}
    (a : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom f0 f1) (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f1 f3) (b : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f0 f2)
    (c : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom f2 f3) (a' : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom g0 g1) (e' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso g1 g3)
    (b' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso g0 g2) (c' : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom g2 g3)
    (h0 : f0 = g0) (h1 : f1 = g1) (h2 : f2 = g2) (h3 : f3 = g3)
    (ha : HEq a a') (he : HEq e e') (hb : HEq b b') (hc : HEq c c')
    (hs : a' ≫ e'.hom = b'.hom ≫ c') : a ≫ e.hom = b.hom ≫ c := by
  have heh := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_hom_heq e e' h1 h3 he
  have hbh := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_hom_heq b b' h0 h2 hb
  have hl := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHom_comp_heq a e.hom a' e'.hom h0 h1 h3 ha heh
  have hr := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHom_comp_heq b.hom c b'.hom c' h0 h2 h3 hbh hc
  exact eq_of_heq (hl.trans ((heq_of_eq hs).trans hr.symm))

private lemma precompModuleArrow
    (R : Type u) [CommRing R] (E : Type v) [DGCategory R E] [Small.{u} E]
    (X Y : Type (max (u + 1) v)) [DGCategory R X] [DGCategory R Y]
    (F0 G0 : DGFunctor R X (RightModule R E)) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F0 G0)
    (p : DGFunctor R Y X) :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R Y (RightModule R E) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPrecomp p t))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F0) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map G0) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map p)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R X (RightModule R E) t)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom_precomp_heq R Y X (RightModule R E) p t

private lemma composeInclusionEquation
    {A X : SSet.{u}} [SSet.Quasicategory X] {f0 f1 f2 f3 f4 : A ⟶ X}
    (a : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom f0 f1) (e1 : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f1 f2) (e2 : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f2 f3)
    (b : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f0 f4) (c : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom f4 f2) (d : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom f4 f3)
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f1 f3) (he : e = e1.trans e2)
    (h1 : a ≫ e1.hom = b.hom ≫ c) (h2 : c ≫ e2.hom = d) :
    a ≫ e.hom = b.hom ≫ d := by
  rw [he, Iso.trans_hom, ← Category.assoc, h1, Category.assoc, h2]

variable (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [DGCategory R C] [Small.{u} C]
  {P : Type (max (u + 1) v)} [DGCategory R P] (F G : DGFunctor R P C)
  (a : ∀ x, ForgetEnrichment.of (Complex R) (F.obj x) ⟶
    ForgetEnrichment.of (Complex R) (G.obj x))
  (h : ∀ x y, F.map x y ≫
      eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) (F.obj x)) (a y) =
      G.map x y ≫ eHomWhiskerRight (Complex R) (a x)
        (ForgetEnrichment.of (Complex R) (G.obj y)))
local notation "I" => DGFunctor.id C
local notation "M" => dgHomGluingBimodule R C C C (I) (I)
local notation "H" => dgIdentityHomGluingFunctor R C F G a h

local notation "L" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C C (M)
local notation "family" => dgHomGluingLoopConeFamily R C C C (I) (I)
local notation "J" => dgSmallPerfectEnvelopeInclusion R C ((L) ⊕ (L)) (family)
local notation "K" => dgPerfectModuleUnderlying R C (J)
local notation "Loop" => dgHomGluingLoopConeSmall R C C C (I) (I)
local notation "DS" => dgHomGluingLoopConeShiftedTarget R C C C (I) (I)
local notation "B" => dgIdentityHomGluingModuleConeFamily R C F G a h
local notation "FS" => DGFunctor.comp (F.comp (dgYoneda R C)) (moduleShiftDG R C 1)
local notation "S" => moduleShiftDG R C (-1)

local notation "η" => dgIdentityInverseRotationImageComparison R C
local notation "β" => dgIdentityHomGluingConeConnectingComparison R C F G a h
local notation "βs" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPostcomp (β) (S)

local notation "U" => DGHomGluingLoopConeBase R C C C (I) (I)
local notation "V" => dgPerfectRealization R (U) C (J)
local notation "GYV" => DGFunctor.comp (DGFunctor.comp (DS) (dgYoneda R (U))) (V)
local notation "G0" => DGFunctor.comp (DS) (K)
local notation "QR" => dgIdentityInverseRotationRealizedConeFamily R C
local notation "CI" => dgIdentityInverseRotationImageConeFamily R C
local notation "MI" => dgIdentityHomGluingInverseRotationModuleSource R C F G a h
local notation "FSS" => DGFunctor.comp (FS) (S)
local notation "LI" => dgModuleNaturalConeInr R C (DGFunctor.comp (B) (S)) (FSS) (βs)
local notation "GE" => dgPerfectRealizationYonedaRestrictedNerveComparison R C (U) (J) (DS)
local notation "GI" => dgIdentityInverseRotationImageConeInr R C
local notation "GR" => dgIdentityInverseRotationRealizedConeInr R C
local notation "ε" => dgIdentityInverseRotationTargetEvaluation R C

/-- 概要：元始域上の実逆回転右軸の同じ代表評価前の全族。
方針：元実右軸を元始域で制限する。
規約：元全関手を保持。使われ方：元包含の実評価像の始域。 -/
def dgIdentityHomGluingInverseRotationTargetFamily : DGFunctor R P (RightModule R C) :=
  (H).comp (GYV)

/-- 概要：元始域上の同じ実逆回転 cone 包含。
方針：元全実包含を元入力関手で前合成する。
規約：元包含を保持。使われ方：元全比較の上指定二単体境界。 -/
def dgIdentityHomGluingInverseRotationRealizedInr :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans (dgIdentityHomGluingInverseRotationTargetFamily R C F G a h)
      ((H).comp (QR)) := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPrecomp (H) (GR)

/-- 概要：元右軸の同じ代表評価を元の二重 shift 右軸へ回収する全比較。
方針：元全評価を前合成し同じ全右軸回収で端点を移す。
規約：元評価全比較を保持。使われ方：元包含境界の始域側全比較。 -/
def dgIdentityHomGluingInverseRotationTargetNerveComparison :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgIdentityHomGluingInverseRotationTargetFamily R C F G a h))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (FSS)) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq ((GE).precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (H)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp (H) (GYV)).symm
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp (H) (G0)).symm.trans
      (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
        (dgIdentityHomGluingInverseRotationImageTarget_restriction R C F G a h)))

/-- 概要：元右軸端点の回収後も同じ元全評価比較を保持する。
方針：元全評価同型の端点移送を回収する。
規約：同じ全同型の型付き一致。使われ方：元実包含 square の端点正規化。 -/
lemma dgIdentityHomGluingInverseRotationTargetNerveComparison_heq :
    HEq (dgIdentityHomGluingInverseRotationTargetNerveComparison R C F G a h)
      ((GE).precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (H))) := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq_heq _ _ _

/-- 概要：元始域の全実入力比較は同じ元包含を元 connecting cone 包含へ運ぶ。
方針：元全実評価 square を前合成して同じ二軸・全入力回収で正規化する。
規約：元実包含・元評価比較を変更しない。
使われ方：同じ全指定逆回転比較との合成。 -/
lemma dgIdentityHomGluingInverseRotationRealizedInputNerveComparison_inr :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R P (RightModule R C)
        (dgIdentityHomGluingInverseRotationRealizedInr R C F G a h) ≫
      (dgIdentityHomGluingInverseRotationRealizedInputNerveComparison R C F G a h).hom =
        (dgIdentityHomGluingInverseRotationTargetNerveComparison R C F G a h).hom ≫
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R P (RightModule R C) (LI) := by
  have hev : (GE).hom = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R (L) (RightModule R C) (ε) :=
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom_spec R (L) (RightModule R C) (ε)).symm
  have hg := (dgIdentityInverseRotationRealizedConeNerveComparison_inr R C).trans
    (congrArg (fun t => t ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R (L) (RightModule R C) (GI)) hev.symm)
  have hr := precompInclusionEquation
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R (L) (RightModule R C) (GR))
    (dgIdentityInverseRotationRealizedConeNerveComparison R C) (GE)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R (L) (RightModule R C) (GI)) hg (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (H))
  exact recoverInclusionSquare
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R P (RightModule R C)
      (dgIdentityHomGluingInverseRotationRealizedInr R C F G a h))
    (dgIdentityHomGluingInverseRotationRealizedInputNerveComparison R C F G a h)
    (dgIdentityHomGluingInverseRotationTargetNerveComparison R C F G a h)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R P (RightModule R C) (LI))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (GYV)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (QR)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (H))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R (L) (RightModule R C) (GR)))
    ((dgIdentityInverseRotationRealizedConeNerveComparison R C).precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (H)))
    ((GE).precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (H)))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (G0)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (CI)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (H))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R (L) (RightModule R C) (GI)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp (H) (GYV)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp (H) (QR))
    (((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp (H) (G0)).symm.trans (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
      (dgIdentityHomGluingInverseRotationImageTarget_restriction R C F G a h))).symm)
    (((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp (H) (CI)).symm.trans (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
      (dgIdentityHomGluingInverseRotationImageConeFamily_restriction R C F G a h))).symm)
    (precompModuleArrow R C (L) P (GYV) (QR) (GR) (H))
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq_heq _ _ _)
    (dgIdentityHomGluingInverseRotationTargetNerveComparison_heq R C F G a h)
    (dgIdentityHomGluingInverseRotationImageConeInr_nerve_restriction R C F G a h).symm hr

local notation "YC" => dgYoneda R C
local notation "ηY" => dgIdentityHomGluingYonedaStrictComparison R C F G a h
local notation "δs" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPostcomp
  (dgModuleNaturalConeConnecting R C (F.comp (YC)) (G.comp (YC)) (ηY)) (S)
local notation "AS" => DGFunctor.comp (dgIdentityHomGluingStrictConeFamily R C F G a h) (S)
local notation "LONG" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransComp (dgModuleNaturalConeInr R C (AS) (FSS) (δs))
  (dgModuleNaturalInverseRotation R C (F.comp (YC)) (G.comp (YC)) (ηY))

/-- 概要：元始域上の全実逆回転比較は元包含を元負符号付き長辺へ運ぶ。
方針：元全実入力比較の包含 square と元指定厳密逆の包含則を合成する。
規約：元実比較・元包含・元長辺を同時に保持。
使われ方：元上指定二単体の二段実評価と固定 ν 全比較への接続。 -/
lemma dgIdentityHomGluingInverseRotationRealizedNerveComparison_inr :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R P (RightModule R C)
        (dgIdentityHomGluingInverseRotationRealizedInr R C F G a h) ≫
      (dgIdentityHomGluingInverseRotationRealizedNerveComparison R C F G a h).hom =
        (dgIdentityHomGluingInverseRotationTargetNerveComparison R C F G a h).hom ≫
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R P (RightModule R C) (LONG) := by
  exact composeInclusionEquation
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R P (RightModule R C)
      (dgIdentityHomGluingInverseRotationRealizedInr R C F G a h))
    (dgIdentityHomGluingInverseRotationRealizedInputNerveComparison R C F G a h)
    (dgIdentityHomGluingInverseRotationStrictNerveComparison R C F G a h)
    (dgIdentityHomGluingInverseRotationTargetNerveComparison R C F G a h)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R P (RightModule R C) (LI))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R P (RightModule R C) (LONG))
    (dgIdentityHomGluingInverseRotationRealizedNerveComparison R C F G a h) rfl
    (dgIdentityHomGluingInverseRotationRealizedInputNerveComparison_inr R C F G a h)
    (dgIdentityHomGluingInverseRotationStrictNerveComparison_inr R C F G a h)
end SerrePositivity.KST.SConstruction
