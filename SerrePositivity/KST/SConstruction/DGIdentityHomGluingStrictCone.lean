module
public import SerrePositivity.KST.SConstruction.DGIdentityHomGluingComparisonZero
public import SerrePositivity.KST.SConstruction.DGClosedComparisonPostcomposition
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConeConnecting
public import SerrePositivity.KST.SConstruction.DGPerfectModuleUnderlying

/-!
概要：元厳密比較の恒等 Hom gluing 表示を、同じ実加群 cone の厳密比較族へ接続する。
方針：元閉比較を Yoneda で後合成し、第三成分零の全 cone 作用を保持する。
規約：任意の Hom gluing 上での厳密自然性を主張しない。
使われ方：実逆回転後の合成全比較を元始域上で構成する。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory HomologicalComplex CochainComplex HomComplex
open DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  {P : Type w} [DGCategory R P] (F G : DGFunctor R P C)
  (a : ∀ x, ForgetEnrichment.of (Complex R) (F.obj x) ⟶
    ForgetEnrichment.of (Complex R) (G.obj x))
  (h : ∀ x y, F.map x y ≫
      eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) (F.obj x)) (a y) =
    G.map x y ≫ eHomWhiskerRight (Complex R) (a x)
      (ForgetEnrichment.of (Complex R) (G.obj y)))
local notation "Y" => dgYoneda R C
local notation "I" => DGFunctor.id C
local notation "H" => dgIdentityHomGluingFunctor R C F G a h

/-- 概要：同じ元比較の Yoneda 像を全次数厳密自然変換へ束ねる。
方針：元閉射と既存の dg 後合成自然性を使う。
規約：元の比較射を保持。使われ方：同じ実 cone 関手の入力。 -/
def dgIdentityHomGluingYonedaStrictComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans (F.comp (Y)) (G.comp (Y)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleStrictNatTransOfHomNaturality R C
    (fun x => (Y).onClosed.map (a x))
    (dgClosedComparison_postcomp_naturality R F G (Y) a h)

/-- 概要：同じ厳密比較族の cone 入力閉射は元 Yoneda 比較射。
方針：閉射と閉元の対応の逆律を使う。
規約：対象別存在選択なし。使われ方：実 cone の対象の厳密回収。 -/
lemma dgIdentityHomGluingYonedaStrictComparison_arrow (x : P) :
    dgModuleNaturalConeArrow R C (F.comp (Y)) (G.comp (Y))
      (dgIdentityHomGluingYonedaStrictComparison R C F G a h) x =
        (Y).onClosed.map (a x) := by
  change (closedHomEquiv R (RightModule R C) _ _).symm
    ((closedHomEquiv R (RightModule R C) _ _) ((Y).onClosed.map (a x))) = _
  exact (closedHomEquiv R (RightModule R C) _ _).symm_apply_apply _

/-- 概要：元比較族上の実 cone を、同じ全 Hom を持つ厳密 dg 関手にする。
方針：同じ Yoneda 比較族へ既存の点ごとの実 cone 関手を適用する。
規約：第三成分零は元厳密比較から実証済み。
使われ方：元逆回転 cone 比較の全自然性の始域。 -/
def dgIdentityHomGluingStrictConeFamily : DGFunctor R P (RightModule R C) :=
  dgModuleNaturalConeFunctor R C (F.comp (Y)) (G.comp (Y))
    (dgIdentityHomGluingYonedaStrictComparison R C F G a h)

/-- 概要：同じ実 cone の対象は元比較射の Yoneda 像の cone。
方針：入力閉射の厳密回収を cone に適用する。
規約：同型な cone へ置換しない。使われ方：元実 cone 対象との照合。 -/
lemma dgIdentityHomGluingStrictConeFamily_obj (x : P) :
    ForgetEnrichment.of (Complex R)
      ((dgIdentityHomGluingStrictConeFamily R C F G a h).obj x) =
      moduleCone R C ((Y).onClosed.map (a x)) :=
  congrArg (fun t => moduleCone R C t)
    (dgIdentityHomGluingYonedaStrictComparison_arrow R C F G a h x)
/-- 概要：元 gluing 表示の加群比較射は同じ Yoneda 後合成射。
方針：元 gluing 比較対象の閉射回収だけを用いる。
規約：全比較の成分を保持。使われ方：同じ実 cone の厳密照合。 -/
lemma dgIdentityHomGluingTargetModuleMap (x : P) :
    dgHomGluingTargetModuleMap R C C C (I) (I) ((H).obj x) =
      (Y).onClosed.map (a x) :=
  congrArg (Y).onClosed.map
    (dgHomGluingTargetMap_comparisonObject R C C C (I) (I) F G a x)

/-- 概要：厳密比較族の元 cone と gluing 表示の元 cone の指定実同型。
方針：同じ二閉射の回収等号だけで輸送する。
規約：対象別の同値を選択しない。使われ方：実逆回転比較の始域輸送。 -/
def dgIdentityHomGluingStrictConeInputIso (x : P) :
    ForgetEnrichment.of (Complex R)
      ((dgIdentityHomGluingStrictConeFamily R C F G a h).obj x) ≅
      moduleCone R C (dgHomGluingTargetModuleMap R C C C (I) (I) ((H).obj x)) :=
  eqToIso ((dgIdentityHomGluingStrictConeFamily_obj R C F G a h x).trans
    (congrArg (fun t => moduleCone R C t)
      (dgIdentityHomGluingTargetModuleMap R C F G a h x)).symm)
end SerrePositivity.KST.SConstruction
