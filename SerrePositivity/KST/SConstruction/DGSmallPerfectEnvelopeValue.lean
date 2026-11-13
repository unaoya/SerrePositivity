module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.FunctorHomTypedWhiskerAlgebra
public import SerrePositivity.KST.SConstruction.DGSmallPerfectEnvelopeNativeProperties
public import SerrePositivity.KST.SConstruction.DGKNativeValueComparison
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.VertexTransport.FunctorIsoTransport

/-!
概要：指定実像を保持する小 Perf 包絡の固定 ν 値を、元基底の固定 ν 値へ戻す。
方針：同じ包絡の native 完備性と、元全 Perf への実包含・同じ固定値評価を使う。
規約：元基底の完備性は要求しない。対象別の代表選択で全比較を代用しない。
使われ方：二段の実逆回転基底と元 resolved 商の頂点照合。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalClosed SSet DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (D : Type (u + 1)) [DGCategory R D] [Small.{u} D]
  (J : Type (u + 1)) [Small.{u} J] (X : J → PerfectDGModule R D)
local notation "C" => DGSmallPerfectEnvelope R D J X

/-- 概要：同じ小包絡の native／固定 ν 指定同値。
方針：同じ実包絡の前三角性と coherent 完備性を使用する。
規約：元指定像を保持。使われ方：固定値の逆比較の始点。 -/
def dgSmallPerfectEnvelopeNativeValueEquivalence : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (C)) (dgKInputStableValue R
      (dgKUniverseInput.{u, u + 1, u + 1} R (C))).obj :=
  (@dgKNativeValueComparison_isQCatEquivalence R _ (C) _ _
    (dgSmallPerfectEnvelope_pretriangulated R D J X)
    (dgSmallPerfectEnvelope_complete R D J X)).choose

/-- 概要：同じ小包絡と元基底の固定 ν 値の指定同値。
方針：元全 Perf への実包含を同じ固定値評価へ接続する。
規約：元基底の coherent 完備性は不要。使われ方：実長方形の共通商頂点。 -/
def dgSmallPerfectEnvelopeValueEquivalence : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence
    (dgKInputStableValue R (dgKUniverseInput.{u, u + 1, u + 1} R (C))).obj
    (dgKInputStableValue R (dgKUniverseInput.{u, u + 1, u + 1} R D)).obj :=
  (dgSmallPerfectEnvelopeNativeValueEquivalence R D J X).symm.trans
    ((dgSmallPerfectEnvelopeNerveEquivalence R D J X).trans
      (dgKNativePerfectValueEquivalence R D))

/-- 概要：同じ値同値は元全 Perf への実包含・評価を全関手同型で回収する。
方針：元 native 比較の単位を同じ全包含・評価で後合成する。
規約：元の全 Hom を保持。使われ方：指定頂点比較と実像の照合。 -/
def dgSmallPerfectEnvelopeValueEquivalence_native : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (dgKNativeValueComparison R (C) ≫
      (dgSmallPerfectEnvelopeValueEquivalence R D J X).hom)
    ((dgSmallPerfectEnvelopeNerveEquivalence R D J X).hom ≫
      (dgKNativePerfectValueEquivalence R D).hom) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq
    ((dgSmallPerfectEnvelopeNativeValueEquivalence R D J X).homInvIso.postcomp
      ((dgSmallPerfectEnvelopeNerveEquivalence R D J X).hom ≫
        (dgKNativePerfectValueEquivalence R D).hom))
    (Category.assoc _ _ _) (Category.id_comp _)

/-- 概要：同じ包絡値比較は任意の指定終域評価の後でも元実像を回収する。
方針：元の全 native 評価比較を後合成し、結合だけを整える。
規約：元同値を保持。使われ方：二段包絡評価の具体化。 -/
def dgSmallPerfectEnvelopeValueEquivalence_native_postcomp
    {Z : SSet.{u + 1}} [Quasicategory Z]
    (e : (dgKInputStableValue R (dgKUniverseInput.{u, u + 1, u + 1} R D)).obj ⟶ Z) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (dgKNativeValueComparison R (C) ≫
      ((dgSmallPerfectEnvelopeValueEquivalence R D J X).hom ≫ e))
      (((dgSmallPerfectEnvelopeNerveEquivalence R D J X).hom ≫
        (dgKNativePerfectValueEquivalence R D).hom) ≫ e) := by
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso, Category.assoc] using
    (dgSmallPerfectEnvelopeValueEquivalence_native R D J X).postcomp e

private lemma envelopeValueNaturality {A0 B0 C0 : SSet.{u}} [Quasicategory B0] [Quasicategory C0]
    {f g : A0 ⟶ B0} {p q : B0 ⟶ C0} (a : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom f g) (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso p q) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp f g p a ≫ (e.precomp g).hom =
      (e.precomp f).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp f g q a := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_hom, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_hom]
  change (hoFunctor.map ((ihom A0).map p)).toFunctor.map a ≫
      (hoFunctor.map ((pre g).app C0)).toFunctor.map e.hom =
    (hoFunctor.map ((pre f).app C0)).toFunctor.map e.hom ≫
      (hoFunctor.map ((ihom A0).map q)).toFunctor.map a
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHom_whisker_exchange a e.hom

/-- 概要：同じ包絡値全比較は元の任意の全関手射に自然。
方針：元の全関手同型と二胞体交換則を使う。
規約：射の可逆性は不要。使われ方：元比較射を保った固定 ν 移送。 -/
lemma dgSmallPerfectEnvelopeValueEquivalence_native_naturality
    {A : SSet.{u + 1}} (f g : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (C)) (a : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom f g) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp f g (dgKNativeValueComparison R (C) ≫
      (dgSmallPerfectEnvelopeValueEquivalence R D J X).hom) a ≫
      ((dgSmallPerfectEnvelopeValueEquivalence_native R D J X).precomp g).hom =
    ((dgSmallPerfectEnvelopeValueEquivalence_native R D J X).precomp f).hom ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp f g ((dgSmallPerfectEnvelopeNerveEquivalence R D J X).hom ≫
        (dgKNativePerfectValueEquivalence R D).hom) a :=
  envelopeValueNaturality a (dgSmallPerfectEnvelopeValueEquivalence_native R D J X)

end SerrePositivity.KST.SConstruction
