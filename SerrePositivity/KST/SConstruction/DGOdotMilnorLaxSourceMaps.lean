module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorLaxInputComparison
public import SerrePositivity.KST.SConstruction.DGOdotMilnorLaxVerdier

/-!
概要：実 lax 包含の二射影を、元 top・side の同じ実小 Perf 延長へ厳密照合する。
方針：D2 の射影等式と、既存の小模型対角の strict dg 合成式を使う。
規約：対象の同型類だけで代用せず全単体の等式を保つ。
使われ方：LT の下二辺と元代数四角形の射の照合。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet DifferentialGraded InfinityCategories LocalizingInvariants
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "A" => _root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R (DGOdotInput.source d)
local notation "B" => _root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R (DGOdotInput.left d)
local notation "D" => _root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R (DGOdotInput.right d)
local notation "V" => _root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R (DGOdotInput.corner d)
local notation "L" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R (DGOdotInput.top d)
local notation "G" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R (DGOdotInput.side d)
local notation "p" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R (DGOdotInput.lower d)
local notation "q" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R (DGOdotInput.upper d)
local notation "CL" => DGSmallPerfectArrowTarget R (A) (B) (L)
local notation "DR" => DGSmallPerfectArrowTarget R (A) (D) (G)
local notation "VT" => DGSmallPerfectSquareCorner R (A) (B) (D) (V) (L) (G) (p) (q)
local notation "pS" => dgSmallPerfectSquareLeftMap R (A) (B) (D) (V) (L) (G) (p) (q)
local notation "qS" => dgSmallPerfectSquareRightMap R (A) (B) (D) (V) (L) (G) (p) (q)
local notation "M" => dgHomGluingBimodule R (CL) (DR) (VT) (pS) (qS)
local instance : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R (DGOdotGluing R d) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnor_isDGPretriangulated R d
local instance : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgOdotQuotientInput R d).diagonal) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorNativeDiagonal_isExactFunctor R d

/-- 概要：元左小 Perf 因子の同宇宙 ULift 表示。
方針：型の ULift 自然同型を使う。規約：全単体を保つ。
使われ方：元 top の実延長との strict 比較。 -/
def dgOdotMilnorLeftLiftIso : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (CL) ≅ (dgOdotMilnorLaxLeft R d).obj :=
  (Functor.isoWhiskerLeft (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (CL)) CategoryTheory.uliftFunctorTrivial ≪≫
    Functor.rightUnitor _).symm

/-- 概要：元右小 Perf 因子の同宇宙 ULift 表示。
方針：型の ULift 自然同型を使う。規約：全単体を保つ。
使われ方：元 side の実延長との strict 比較。 -/
def dgOdotMilnorRightLiftIso : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (DR) ≅ (dgOdotMilnorLaxRight R d).obj :=
  (Functor.isoWhiskerLeft (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (DR)) CategoryTheory.uliftFunctorTrivial ≪≫
    Functor.rightUnitor _).symm

/-- 概要：元左射影の宇宙共通化は同じ strict native 射影と可換。
方針：同じ全単体の実作用を比較する。規約：表示以外の選択を加えない。
使われ方：lax 第一射影の元の射への回収。 -/
lemma dgOdotMilnorNativeLeftProjection_lift :
    (dgOdotMilnorNativeLiftIso R d).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseLeftNerve R (CL) (DR) (M) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeft R (CL) (DR) (M)) ≫ (dgOdotMilnorLeftLiftIso R d).hom := by
  ext n a
  rfl

/-- 概要：元右射影の宇宙共通化も同じ strict native 射影と可換。
方針：同じ全単体の実作用を比較する。規約：表示以外の選択を加えない。
使われ方：lax 第二射影の元の射への回収。 -/
lemma dgOdotMilnorNativeRightProjection_lift :
    (dgOdotMilnorNativeLiftIso R d).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseRightNerve R (CL) (DR) (M) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRight R (CL) (DR) (M)) ≫ (dgOdotMilnorRightLiftIso R d).hom := by
  ext n a
  rfl

/-- 概要：実 lax 包含後の第一射影は元 top の実小 Perf 延長そのもの。
方針：D2 の同じ射影式と元対角の dg 合成式を nerve に移す。
規約：元の四角形の射を選び直さない。使われ方：LT の下辺。 -/
lemma dgOdotMilnorLaxInclusion_fst_original :
    (dgOdotMilnorLaxInclusion R d).hom ≫
      (laxFst (dgOdotMilnorLaxYoneda R d) (dgOdotMilnorLaxCoefficient R d)).hom =
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgSmallPerfectArrow R (A) (B) (L)) ≫ (dgOdotMilnorLeftLiftIso R d).hom := by
  change ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorNativeDiagonal R d).hom ≫
    (dgOdotMilnorNativeLaxComparison R d).hom) ≫ _ = _
  rw [Category.assoc, dgOdotMilnorNativeLaxComparison_fst,
    dgOdotMilnorNativeLeftProjection_lift]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgOdotQuotientInput R d).diagonal ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeft R (CL) (DR) (M)) ≫
      (dgOdotMilnorLeftLiftIso R d).hom) = _
  rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp]
  exact congrArg (fun F => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F ≫ (dgOdotMilnorLeftLiftIso R d).hom)
    (dgSmallPerfectSquareDiagonal_left R (A) (B) (D) (V) (L) (G) (p) (q)
      (dgOdotInput_dg_commutes R d))

/-- 概要：実 lax 包含後の第二射影は元 side の実小 Perf 延長そのもの。
方針：D2 の同じ射影式と元対角の dg 合成式を nerve に移す。
規約：元二射影の順序を保つ。使われ方：LT の左辺。 -/
lemma dgOdotMilnorLaxInclusion_snd_original :
    (dgOdotMilnorLaxInclusion R d).hom ≫
      (laxSnd (dgOdotMilnorLaxYoneda R d) (dgOdotMilnorLaxCoefficient R d)).hom =
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgSmallPerfectArrow R (A) (D) (G)) ≫ (dgOdotMilnorRightLiftIso R d).hom := by
  change ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorNativeDiagonal R d).hom ≫
    (dgOdotMilnorNativeLaxComparison R d).hom) ≫ _ = _
  rw [Category.assoc, dgOdotMilnorNativeLaxComparison_snd,
    dgOdotMilnorNativeRightProjection_lift]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgOdotQuotientInput R d).diagonal ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRight R (CL) (DR) (M)) ≫
      (dgOdotMilnorRightLiftIso R d).hom) = _
  rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp]
  exact congrArg (fun F => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F ≫ (dgOdotMilnorRightLiftIso R d).hom)
    (dgSmallPerfectSquareDiagonal_right R (A) (B) (D) (V) (L) (G) (p) (q)
      (dgOdotInput_dg_commutes R d))

end SerrePositivity.KST.SConstruction
