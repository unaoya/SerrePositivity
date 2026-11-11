module
public import SerrePositivity.KST.SConstruction.DGOdotTargetSmallInputComparison
public import SerrePositivity.KST.SConstruction.DGKInputClosedComparisonImage
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGNativeLabel

/-! # 元の cone 入力比較の ν 像と同じ一回 Perf 延長の成分
概要：同じ固定 S 内の cone 比較を、同じ実 Perf 延長の順逆成分で読む。
方針：標準区間比較の ν 像と native ラベル評価を使い、元の標準合成比較を保持する。
規約：元の入力閉同型を変更しない。使われ方：相対 Land–Tamme 長方形の終域比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Opposite Simplicial SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "PIn" => dgOdotAlgebraInput R d
local notation "QIn" => dgOdotTargetSmallInput R d
local notation "fCone" => dgOdotConeAlgebraSmallInputMap R d
local notation "gTarget" => dgOdotTargetAlgebraSmallInputMap R d
local notation "eCone" => dgOdotAlgebraSmallInputIso R d

/-- 元の cone 入力同型を、各実 perfect 入力の同じ一回延長に作用させた実同型。 -/
def dgOdotAlgebraSmallInputPerfectIso (M : PerfectDGModule R (PIn)) :=
  (perfectDGExtensionInputFunctorAt R (PIn) (QIn) M).onClosed.mapIso (eCone)

/-- 同じ cone 入力同型を、固定 ν の元の各ラベルに作用させた実同型。 -/
def dgOdotAlgebraSmallInputLabelIso (X : PresentedPerfectDGObject R (PIn)) :=
  (presentedPerfectDGLabelAction R (PIn) (QIn) X).onClosed.mapIso (eCone)

/-- 元の native cone 比較のラベル成分は、同じ実入力同型の順射の実辺。 -/
lemma dgOdotAlgebraSmallInputLabelIso_native (X : PresentedPerfectDGObject R (PIn)) :
    (presentedPerfectDGNativeCoreAction R (PIn) (QIn)).app (op ⦋1⦌)
        (dgNativePointSimplex R (PresentedPerfectDGObject R (PIn)) X 1,
          ULift.up (dgFunctorClosedIsoNativeEdge R (PIn) (QIn)
            (fCone).down (gTarget).down (eCone)).edge) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R (PresentedPerfectDGObject R (QIn))
        (dgOdotAlgebraSmallInputLabelIso R d X).hom).edge :=
  presentedPerfectDGNativeCoreAction_label_closed R (PIn) (QIn) X _ _ (eCone)

/-- 同じ native 比較の順成分は、元の一回 Perf 延長の順成分を同じ合成比較で共役したもの。 -/
lemma dgOdotAlgebraSmallInputLabelIso_hom (X : PresentedPerfectDGObject R (PIn)) :
    ForgetEnrichment.homTo (Complex R) (dgOdotAlgebraSmallInputLabelIso R d X).hom =
      ForgetEnrichment.homTo (Complex R)
        (dgOdotAlgebraSmallInputPerfectIso R d (presentedPerfectDGValue R (PIn) X)).hom ≫
          enrichedClosedIsoConjugation (Complex R)
            (presentedPerfectDGActionIso R (PIn) (QIn) (fCone).down X)
            (presentedPerfectDGActionIso R (PIn) (QIn) (gTarget).down X) :=
  presentedPerfectDGLabelAction_closed_perfect R (PIn) (QIn) X _ _ (eCone).hom

/-- 同じ native 比較の逆成分も、元の一回 Perf 延長の逆成分と同じ合成比較を保持する。 -/
lemma dgOdotAlgebraSmallInputLabelIso_inv (X : PresentedPerfectDGObject R (PIn)) :
    ForgetEnrichment.homTo (Complex R) (dgOdotAlgebraSmallInputLabelIso R d X).inv =
      ForgetEnrichment.homTo (Complex R)
        (dgOdotAlgebraSmallInputPerfectIso R d (presentedPerfectDGValue R (PIn) X)).inv ≫
          enrichedClosedIsoConjugation (Complex R)
            (presentedPerfectDGActionIso R (PIn) (QIn) (gTarget).down X)
            (presentedPerfectDGActionIso R (PIn) (QIn) (fCone).down X) :=
  presentedPerfectDGLabelAction_closed_perfect R (PIn) (QIn) X _ _ (eCone).inv

/-- 元の実 cone 比較四角形全体の ν 像は、同じ実入力区間の元の豊穣作用の標準比較。 -/
lemma dgOdotAlgebraSmallNuSquare_native :
    dgOdotAlgebraSmallNuSquare R d =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (dgKInputClosedIsoNuParameter R (fCone) (gTarget) (eCone) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison (presentedPerfectDGStableQCat R (PIn))
          (presentedPerfectDGStableQCat R (QIn))) :=
  dgKInputClosedIsoSquare_nu R (fCone) (gTarget) (eCone)

end SerrePositivity.KST.SConstruction
