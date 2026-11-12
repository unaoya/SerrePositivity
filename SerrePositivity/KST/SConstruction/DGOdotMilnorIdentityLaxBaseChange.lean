module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorIdentityValueEquivalences
public import SerrePositivity.KST.LocalizingInvariants.IdentityLaxDiagonal
public import SerrePositivity.KST.LocalizingInvariants.CofiberFamilyExactComparison
public import SerrePositivity.KST.LocalizingInvariants.CofiberFamilyPrecomposition

/-!
概要：同じ小 Perf 基底の恒等 lax 圏を、元 resolved 商の固定 ν 値の恒等 lax 圏へ移す。
方針：Sp 正本の矢印圏表示と元基底値同値の全内部 Hom 作用を合成する。
規約：元の両射影・対角・差の全自然性を保持。dg gluing との全比較は別工程。
使われ方：D2 の恒等比較を LT 右面の同じ完備化先へ接続する。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial
private lemma identityBaseEvaluation {X Y : SSet.{u}} (f : X ⟶ Y) (i : Fin 2) :
    (ihom (Δ[1] : SSet.{u})).map f ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := Y) (stdSimplex.obj₀Equiv.symm i) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) (stdSimplex.obj₀Equiv.symm i) ≫ f := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  rfl
private lemma identityBaseEndpoint {A B X Y : SSet.{u}}
    (f : A ⟶ B) (e : X ⟶ Y)
    (a : A ⟶ (ihom (Δ[1] : SSet.{u})).obj X)
    (b : B ⟶ (ihom (Δ[1] : SSet.{u})).obj Y) (i : Fin 2)
    (p : A ⟶ X) (q : B ⟶ Y)
    (ha : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm i) = p)
    (hb : b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm i) = q)
    (h : f ≫ b = a ≫ (ihom (Δ[1] : SSet.{u})).map e) : f ≫ q = p ≫ e := by
  rw [← hb, ← Category.assoc, h, Category.assoc, identityBaseEvaluation,
    ← Category.assoc, ha]

private lemma identityBaseDiagonal {X Y : SSet.{u}} (e : X ⟶ Y)
    (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullback (𝟙 X) (𝟙 X) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullback (𝟙 Y) (𝟙 Y))
    (h : f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackArrow (𝟙 Y) (𝟙 Y) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackArrow (𝟙 X) (𝟙 X) ≫ (ihom (Δ[1] : SSet.{u})).map e) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap (Δ[1] : SSet.{u}) X ≫ _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.arrowLaxInverse X) ≫ f =
      e ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap (Δ[1] : SSet.{u}) Y ≫ _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.arrowLaxInverse Y) := by
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.arrowLaxIso Y).hom).1
  change ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap (Δ[1] : SSet.{u}) X ≫ _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.arrowLaxInverse X) ≫ f) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackArrow (𝟙 Y) (𝟙 Y) = _
  calc
    _ = (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap (Δ[1] : SSet.{u}) X ≫ _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.arrowLaxInverse X) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackArrow (𝟙 X) (𝟙 X) ≫
          (ihom (Δ[1] : SSet.{u})).map e) :=
      (Category.assoc _ _ _).trans (congrArg (fun k =>
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap (Δ[1] : SSet.{u}) X ≫ _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.arrowLaxInverse X) ≫ k) h)
    _ = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap (Δ[1] : SSet.{u}) X ≫
        (ihom (Δ[1] : SSet.{u})).map e := by
      rw [← Category.assoc, Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap _ _),
        _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.arrowLaxInverse_arrow, Category.comp_id]
    _ = e ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap (Δ[1] : SSet.{u}) Y := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap_postcomp _ e
    _ = _ := by
      change e ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap (Δ[1] : SSet.{u}) Y =
        (e ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap (Δ[1] : SSet.{u}) Y ≫ _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.arrowLaxInverse Y)) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackArrow (𝟙 Y) (𝟙 Y)
      rw [Category.assoc, Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.arrowLaxInverse_arrow, Category.comp_id]

variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "C" => dgKInputStableValue R (dgOdotMilnorIdentityBaseInput R d)
local notation "Q" => dgKInputStableValue R (dgOdotMilnorResolvedInput R d)
local notation "e" => dgOdotMilnorIdentityBaseValueEquivalence R d

/-- 概要：元基底値同値は恒等 lax 圏全体の同値を誘導する。
方針：同じ矢印圏表示の間で全内部 Hom 後合成を行う。
規約：実全単体を保持。使われ方：LT 右面の中央頂点比較。 -/
def dgOdotMilnorIdentityLaxBaseChange : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence
    (laxCategory (𝟙 (C)) (𝟙 (C))).obj (laxCategory (𝟙 (Q)) (𝟙 (Q))).obj :=
  ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.arrowLaxIso (C).obj)).trans
    ((e).postcompose (Δ[1] : SSet.{u + 1}))).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.arrowLaxIso (Q).obj).symm)

/-- 概要：基底変更は元の矢印全族を厳密に回収する。
方針：Sp の矢印圏表示の往復等号を使う。規約：全関手の等号。
使われ方：両射影・対角・cofiber 差の自然比較の共通入力。 -/
lemma dgOdotMilnorIdentityLaxBaseChange_arrow :
    (dgOdotMilnorIdentityLaxBaseChange R d).hom ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackArrow (𝟙 (Q).obj) (𝟙 (Q).obj) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackArrow (𝟙 (C).obj) (𝟙 (C).obj) ≫
        (ihom (Δ[1] : SSet.{u + 1})).map (e).hom := by
  change (((_root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.arrowLaxIso (C).obj).hom ≫
      (ihom (Δ[1] : SSet.{u + 1})).map (e).hom) ≫
        (_root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.arrowLaxIso (Q).obj).inv) ≫ (_root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.arrowLaxIso (Q).obj).hom = _
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

/-- 概要：元の第一射影は同じ基底値同値と全単体で可換。
方針：元矢印族の始点を評価する。規約：元の射影を変更しない。
使われ方：右面の指定第一成分。 -/
lemma dgOdotMilnorIdentityLaxBaseChange_fst :
    (dgOdotMilnorIdentityLaxBaseChange R d).hom ≫
        (laxFst (𝟙 (Q)) (𝟙 (Q))).hom =
      (laxFst (𝟙 (C)) (𝟙 (C))).hom ≫ (e).hom := by
  exact identityBaseEndpoint (dgOdotMilnorIdentityLaxBaseChange R d).hom (e).hom
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackArrow (𝟙 (C).obj) (𝟙 (C).obj))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackArrow (𝟙 (Q).obj) (𝟙 (Q).obj)) 0
    (laxFst (𝟙 (C)) (𝟙 (C))).hom
    (laxFst (𝟙 (Q)) (𝟙 (Q))).hom
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackArrow_source _ _).trans (Category.comp_id _))
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackArrow_source _ _).trans (Category.comp_id _))
    (dgOdotMilnorIdentityLaxBaseChange_arrow R d)

/-- 概要：元の第二射影も同じ基底値同値と全単体で可換。
方針：元矢印族の終点を評価する。規約：因子の順序を保持。
使われ方：右面の指定第二成分。 -/
lemma dgOdotMilnorIdentityLaxBaseChange_snd :
    (dgOdotMilnorIdentityLaxBaseChange R d).hom ≫
        (laxSnd (𝟙 (Q)) (𝟙 (Q))).hom =
      (laxSnd (𝟙 (C)) (𝟙 (C))).hom ≫ (e).hom := by
  exact identityBaseEndpoint (dgOdotMilnorIdentityLaxBaseChange R d).hom (e).hom
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackArrow (𝟙 (C).obj) (𝟙 (C).obj))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackArrow (𝟙 (Q).obj) (𝟙 (Q).obj)) 1
    (laxSnd (𝟙 (C)) (𝟙 (C))).hom
    (laxSnd (𝟙 (Q)) (𝟙 (Q))).hom
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackArrow_target _ _).trans (Category.comp_id _))
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackArrow_target _ _).trans (Category.comp_id _))
    (dgOdotMilnorIdentityLaxBaseChange_arrow R d)

/-- 概要：恒等対角は元基底値同値と全単体で可換。
方針：矢印表示の可消去性と元定値関手の全自然性を使う。
規約：対角の厳密等号。使われ方：LT 右面の指定包含辺比較。 -/
lemma dgOdotMilnorIdentityLaxBaseChange_diagonal :
    (IdentityLax.exactDiagonal (C)).hom ≫ (dgOdotMilnorIdentityLaxBaseChange R d).hom =
      (e).hom ≫ (IdentityLax.exactDiagonal (Q)).hom := by
  exact identityBaseDiagonal (e).hom (dgOdotMilnorIdentityLaxBaseChange R d).hom
    (dgOdotMilnorIdentityLaxBaseChange_arrow R d)

/-- 概要：同じ実 cofiber 差は基底値同値と全関手同型で可換。
方針：元矢印族の厳密回収を Sp 正本の cofiber 完全自然性へ渡す。
規約：対象別比較へ弱めない。使われ方：LT 右面の指定商辺比較。 -/
def dgOdotMilnorIdentityLaxBaseChange_difference : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    ((dgOdotMilnorIdentityLaxBaseChange R d).hom ≫
      (exactLaxDifference (𝟙 (Q)) (𝟙 (Q))).hom)
    ((exactLaxDifference (𝟙 (C)) (𝟙 (C))).hom ≫ (e).hom) := by
  letI : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (e).hom := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_isQCatEquivalence (e).isQCatEquivalence
  let a := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackArrow (𝟙 (C).obj) (𝟙 (C).obj)
  let b := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackArrow (𝟙 (Q).obj) (𝟙 (Q).obj)
  have p := CofiberFamily.precompositionIso b (dgOdotMilnorIdentityLaxBaseChange R d).hom
  have t := CofiberFamily.familyExactComparison (e).hom a
  exact (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq p rfl (congrArg (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberSquareFamily.cofiber (Q).obj)
    (dgOdotMilnorIdentityLaxBaseChange_arrow R d))).trans t.symm
end SerrePositivity.KST.SConstruction
