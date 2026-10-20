module
public import SerrePositivity.InfinityCategories.Derived.DGFiniteRoofCompositeDiagram
public import SerrePositivity.InfinityCategories.F1B.HomotopyWhiskering

/-!
概要：共通実細分を任意パラメータへ制限し、元の二輸送と合成候補を保持する。
方針：同じ二始域・二分母を保ち、全実ホモトピーを前合成する。
規約：制限先の有限性を仮定しない。使われ方：全降下選択空間との積への展開。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (P : Set D) {K L : SSet.{max u v}} (i : L ⟶ K)
/-- 一つの実閉分母による表示を、分母と元図式への輸送を保持して制限する。 -/
def dgFiniteRoofPresentationPrecomp {x y : D} {r : K ⟶ dgRoofCorrespondence A D P x y}
    (R : DGFiniteRoofPresentation A D P x y r) :
    DGFiniteRoofPresentation A D P x y (i ≫ r) where
  denominator := R.denominator
  coefficient := i ≫ R.coefficient
  transport := stableHomotopyRetarget (functorHomotopyPrecomp R.transport i)
    (Category.assoc _ _ _).symm rfl
/-- 実 Ore 細分を、二分母・二始域・実比較を保持して任意パラメータへ制限する。 -/
def dgFiniteOreRefinementPrecomp {x y z : D} {f : K ⟶ DGNerve.pinchedHom A D x y}
    {s : ForgetEnrichment.of (Complex A) z ⟶ ForgetEnrichment.of (Complex A) y}
    (R : DGFiniteOreRefinement A D P f s) : DGFiniteOreRefinement A D P (i ≫ f) s where
  source := R.source
  denominator := R.denominator
  denominator_mem := R.denominator_mem
  refinedSource := R.refinedSource
  refinement := R.refinement
  refinement_mem := R.refinement_mem
  lift := i ≫ R.lift
  homotopy := stableHomotopyRetarget (functorHomotopyPrecomp R.homotopy i)
    (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm
/-- 二屋根図式の共通実細分を、任意のパラメータ射に沿って制限する。 -/
def dgFiniteRoofOreDataPrecomp {x y z : D}
    {r : K ⟶ dgRoofCorrespondence A D P x y} {s : K ⟶ dgRoofCorrespondence A D P y z}
    (R : DGFiniteRoofOreData A D P x y z r s) :
    DGFiniteRoofOreData A D P x y z (i ≫ r) (i ≫ s) where
  first := dgFiniteRoofPresentationPrecomp A D P i R.first
  second := dgFiniteRoofPresentationPrecomp A D P i R.second
  ore := dgFiniteOreRefinementPrecomp A D P i R.ore
omit [Small.{u} D] in
/-- 元の屋根図式への輸送は、同じ全時刻の写像の制限。 -/
lemma dgFiniteRoofPresentationPrecomp_transport_h {x y : D}
    {r : K ⟶ dgRoofCorrespondence A D P x y} (R : DGFiniteRoofPresentation A D P x y r) :
    (dgFiniteRoofPresentationPrecomp A D P i R).transport.h =
      (i ▷ (Δ[1] : SSet.{max u v})) ≫ R.transport.h := rfl
/-- 実 Ore 比較も、同じ全時刻の写像の制限。 -/
lemma dgFiniteOreRefinementPrecomp_homotopy_h {x y z : D}
    {f : K ⟶ DGNerve.pinchedHom A D x y}
    {s : ForgetEnrichment.of (Complex A) z ⟶ ForgetEnrichment.of (Complex A) y}
    (R : DGFiniteOreRefinement A D P f s) :
    (dgFiniteOreRefinementPrecomp A D P i R).homotopy.h =
      (i ▷ (Δ[1] : SSet.{max u v})) ≫ R.homotopy.h := rfl
/-- パラメータの制限は、実合成分母を変えない。 -/
lemma dgFiniteOreRefinementPrecomp_combinedDenominator {x y z : D}
    {f : K ⟶ DGNerve.pinchedHom A D x y}
    {s : ForgetEnrichment.of (Complex A) z ⟶ ForgetEnrichment.of (Complex A) y}
    (R : DGFiniteOreRefinement A D P f s) :
    (dgFiniteOreRefinementPrecomp A D P i R).combinedDenominator = R.combinedDenominator := rfl
variable {x y z : D} {r : K ⟶ dgRoofCorrespondence A D P x y}
variable {s : K ⟶ dgRoofCorrespondence A D P y z}
variable (R : DGFiniteRoofOreData A D P x y z r s)
/-- 合成分子の族は、パラメータの制限と厳密に可換する。 -/
lemma dgFiniteRoofOreDataPrecomp_compositeNumerator :
    (dgFiniteRoofOreDataPrecomp A D P i R).compositeNumerator = i ≫ R.compositeNumerator :=
  (pinchedHomCompositionFamily_precomp R.ore.lift R.second.coefficient i).symm
variable [IsDGPretriangulated A D]
/-- 合成屋根の実閉分母自体を厳密に保持する。 -/
lemma dgFiniteRoofOreDataPrecomp_compositeDenominator :
    (dgFiniteRoofOreDataPrecomp A D P i R).compositeDenominator = R.compositeDenominator := rfl
/-- 合成候補の元の実屋根図式も、パラメータの制限と厳密に可換する。 -/
lemma dgFiniteRoofOreDataPrecomp_compositeDiagram :
    (dgFiniteRoofOreDataPrecomp A D P i R).compositeDiagram = i ≫ R.compositeDiagram := by
  exact (congrArg (fun a => a ≫ dgClosedRoofHomInclusion A D P x z R.compositeDenominator)
    (dgFiniteRoofOreDataPrecomp_compositeNumerator A D P i R)).trans (Category.assoc _ _ _)
end SerrePositivity.InfinityCategories
