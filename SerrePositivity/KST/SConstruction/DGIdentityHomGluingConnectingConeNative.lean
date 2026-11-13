module
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConePrecompositionNative
public import SerrePositivity.KST.SConstruction.DGIdentityHomGluingConeConnectingTriangle
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.VertexTransport.FunctorIsoTransport

/-!
概要：元 gluing 入力同型を保つ connecting cone の native 全比較。
方針：同じ指定入力比較と実 connecting の全厳密合成等号を使う。
規約：元の cone 族・全ホモトピーを保持する。
使われ方：元実逆回転と固定 ν の全合成比較への入力。
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
local notation "η" => dgIdentityHomGluingYonedaStrictComparison R C F G a h
local notation "δ" => dgModuleNaturalConeConnecting R C (F.comp (J)) (G.comp (J)) (η)
local notation "α" => dgIdentityHomGluingStrictConeInputComparison R C F G a h
local notation "β" => dgIdentityHomGluingConeConnectingComparison R C F G a h
local notation "γ" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransComp (α) (β)

/-- 概要：元指定 cone 入力比較の閉成分は K(C) 同値。
方針：同じ元指定入力同型の閉射を回収する。
規約：入力同型を選び直さない。使われ方：同じ cone 全比較の可逆性。 -/
lemma dgIdentityHomGluingConnectingConeInput_isIso (x : P) :
    IsIso ((moduleToHomotopy R C).map
      (dgModuleNaturalConeArrow R C (A) (B) (α) x)) := by
  rw [dgIdentityHomGluingStrictConeInputComparison_arrow]
  change IsIso ((moduleToHomotopy R C).map
    (dgIdentityHomGluingStrictConeTypedInputIso R C F G a h x).hom)
  exact (moduleToHomotopy R C).map_isIso _

/-- 概要：全合成等号は同じ元 connecting cone 族の等号を与える。
方針：同じ cone 構成へ全厳密合成等号を適用。
規約：元二端点を保持。使われ方：native 全比較の始域回収。 -/
lemma dgIdentityHomGluingConnectingCone_source :
    dgModuleNaturalConeFunctor R C (A) (FS) (γ) =
      dgModuleNaturalConeFunctor R C (A) (FS) (δ) :=
  congrArg (dgModuleNaturalConeFunctor R C (A) (FS))
    (dgIdentityHomGluingConeConnectingComparison_input R C F G a h)

/-- 概要：元実 connecting cone と元自然 connecting cone の指定全比較。
方針：同じ入力比較による cone 全比較の始域を全合成等号で回収。
規約：元全ホモトピーを輸送し成分選択をしない。
使われ方：元実逆回転後の全比較の入力同型因子。 -/
def dgIdentityHomGluingConnectingConeNerveComparison :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgModuleNaturalConeFunctor R C (A) (FS) (δ)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgModuleNaturalConeFunctor R C (B) (FS) (β))) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq
    (dgModuleNaturalConePrecompositionNerveComparison R C (A) (B) (FS) (α) (β)
      (dgIdentityHomGluingConnectingConeInput_isIso R C F G a h))
    (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgIdentityHomGluingConnectingCone_source R C F G a h)) rfl

/-- 概要：回収した全比較は元指定前合成 cone 全比較そのもの。
方針：端点輸送の型付き回収を適用。
規約：全比較の値を変更しない。使われ方：元実成分と指定境界の回収。 -/
lemma dgIdentityHomGluingConnectingConeNerveComparison_heq :
    HEq (dgIdentityHomGluingConnectingConeNerveComparison R C F G a h)
      (dgModuleNaturalConePrecompositionNerveComparison R C (A) (B) (FS) (α) (β)
        (dgIdentityHomGluingConnectingConeInput_isIso R C F G a h)) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq_heq _ _ _
end SerrePositivity.KST.SConstruction
