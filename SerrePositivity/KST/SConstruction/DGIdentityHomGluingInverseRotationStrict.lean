module
public import SerrePositivity.KST.SConstruction.DGIdentityHomGluingShiftedConnecting

/-!
概要：元指定入力逆の同じ全厳密前比較で実逆回転比較を構成する。
方針：入力全比較の native 逆を選ぶ代わりに元厳密逆を cone 構成へ渡す。
規約：元閉成分・同じ零ホモトピー square を保持する。
使われ方：実 gluing 逆回転射と元第二 Yoneda 族の同じ全合成比較。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  {P : Type (max (u + 1) v)} [DGCategory R P] (F G : DGFunctor R P C)
  (a : ∀ x, ForgetEnrichment.of (Complex R) (F.obj x) ⟶
    ForgetEnrichment.of (Complex R) (G.obj x))
  (h : ∀ x y, F.map x y ≫
      eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) (F.obj x)) (a y) =
      G.map x y ≫ eHomWhiskerRight (Complex R) (a x)
        (ForgetEnrichment.of (Complex R) (G.obj y)))
local notation "J" => dgYoneda R C
local notation "A" => dgIdentityHomGluingStrictConeFamily R C F G a h
local notation "B" => dgIdentityHomGluingModuleConeFamily R C F G a h
local notation "FS" => DGFunctor.comp (F.comp (J)) (moduleShiftDG R C 1)
local notation "S" => moduleShiftDG R C (-1)
local notation "η" => dgIdentityHomGluingYonedaStrictComparison R C F G a h
local notation "δ" => dgModuleNaturalConeConnecting R C (F.comp (J)) (G.comp (J)) (η)
local notation "α" => dgIdentityHomGluingStrictConeInputComparison R C F G a h
local notation "β" => dgIdentityHomGluingConeConnectingComparison R C F G a h
local notation "αs" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPostcomp (α) (S)
local notation "βs" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPostcomp (β) (S)
local notation "δs" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPostcomp (δ) (S)


local notation "κ" => dgIdentityHomGluingStrictConeInputInvComparison R C F G a h
local notation "κs" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPostcomp (κ) (S)

/-- 概要：元指定入力逆と元 connecting の逆 shift 合成は実 connecting の逆 shift。
方針：元実 connecting の定義と全厳密合成の後合成保存を使う。
規約：同じ厳密逆成分。使われ方：実 cone 比較の始域回収。 -/
lemma dgIdentityHomGluingInverseRotationStrict_input :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransComp (κs) (δs) = (βs) := by
  exact dgStrictCompositionPostcomp (κ) (δ) (S)

/-- 概要：元指定入力逆の逆 shift 閉成分は K(C) 同値。
方針：元実 shift 射を回収して同じ指定逆同型の同値を写す。
規約：元逆成分を選び直さない。使われ方：実 cone 全比較の可逆性。 -/
lemma dgIdentityHomGluingInverseRotationStrictInput_isIso (x : P) :
    IsIso ((moduleToHomotopy R C).map
      (dgModuleNaturalConeArrow R C ((B).comp (S)) ((A).comp (S)) (κs) x)) := by
  rw [dgModuleNaturalConeShiftArrow]
  apply dgModuleShiftMap_isIso
  rw [dgIdentityHomGluingStrictConeInputInvComparison_arrow]
  change IsIso ((moduleToHomotopy R C).map
    (dgIdentityHomGluingStrictConeTypedInputIso R C F G a h x).inv)
  exact (moduleToHomotopy R C).map_isIso _

/-- 概要：同じ厳密逆 cone 合成の始域は元実 connecting の逆 shift cone。
方針：同じ全合成等号を cone 関手へ適用する。
規約：元全関手の等号。使われ方：全実逆回転比較の始域回収。 -/
lemma dgIdentityHomGluingInverseRotationStrict_source :
    dgModuleNaturalConeFunctor R C ((B).comp (S)) ((FS).comp (S))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransComp (κs) (δs)) =
        dgIdentityHomGluingInverseRotationModuleSource R C F G a h :=
  congrArg (dgModuleNaturalConeFunctor R C ((B).comp (S)) ((FS).comp (S)))
    (dgIdentityHomGluingInverseRotationStrict_input R C F G a h)

/-- 概要：元実逆回転 cone から元第二 Yoneda 族への同じ指定厳密逆を使う全比較。
方針：指定入力厳密逆による実 cone 全比較と元全実逆回転を合成する。
規約：native 入力比較の逆の選択で前辺を代用しない。
使われ方：実 gluing の指定元成分を保つ全合成比較。 -/
def dgIdentityHomGluingInverseRotationStrictNerveComparison :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgIdentityHomGluingInverseRotationModuleSource R C F G a h))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (G.comp (J))) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq
    ((dgModuleNaturalConePrecompositionNerveComparison R C ((B).comp (S)) ((A).comp (S))
      ((FS).comp (S)) (κs) (δs)
      (dgIdentityHomGluingInverseRotationStrictInput_isIso R C F G a h)).trans
        (dgModuleNaturalInverseRotationNerveComparison R C (F.comp (J)) (G.comp (J)) (η)))
    (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgIdentityHomGluingInverseRotationStrict_source R C F G a h)) rfl

/-- 概要：端点回収後の比較は同じ指定厳密逆と元三因子の全合成比較。
方針：型付き端点輸送の回収を使う。
規約：全比較の値を変更しない。使われ方：元実射の成分照合。 -/
lemma dgIdentityHomGluingInverseRotationStrictNerveComparison_heq :
    HEq (dgIdentityHomGluingInverseRotationStrictNerveComparison R C F G a h)
      ((dgModuleNaturalConePrecompositionNerveComparison R C ((B).comp (S)) ((A).comp (S))
        ((FS).comp (S)) (κs) (δs)
        (dgIdentityHomGluingInverseRotationStrictInput_isIso R C F G a h)).trans
          (dgModuleNaturalInverseRotationNerveComparison R C (F.comp (J)) (G.comp (J)) (η))) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq_heq _ _ _
end SerrePositivity.KST.SConstruction
