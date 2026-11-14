module
public import SerrePositivity.KST.SConstruction.DGOdotTargetRawRepresentation
public import SerrePositivity.KST.SConstruction.DGClosedComparisonFromParameter

/-! # 評価した元の商 cone と元の終域 End 比較の全 Hom 照合
概要：元の三段対象同型は、元の比較 End 射の自由代表作用に全次数で自然。
方針：評価した cone 比較の単位パラメータ自然性を回収し、同じ二段右点比較と合成する。
規約：元の閉同型・元の End 比較を保持。使われ方：同じ実 ⊙ 比較の代表加群作用。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "A" => _root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R (DGOdotInput.source d)
local notation "CRaw" => _root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R (DGOdotInput.left d)
local notation "DRaw" => _root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R (DGOdotInput.right d)
local notation "E" => _root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R (DGOdotInput.corner d)
local notation "L" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R (DGOdotInput.top d)
local notation "gRaw" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R (DGOdotInput.side d)
local notation "p" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R (DGOdotInput.lower d)
local notation "q" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R (DGOdotInput.upper d)
local notation "CL" => DGSmallPerfectArrowTarget R (A) (CRaw) (L)
local notation "DR" => DGSmallPerfectArrowTarget R (A) (DRaw) (gRaw)
local notation "pS" => dgSmallPerfectSquareLeftMap R (A) (CRaw) (DRaw) (E) (L) (gRaw) (p) (q)
local notation "qS" => dgSmallPerfectSquareRightMap R (A) (CRaw) (DRaw) (E) (L) (gRaw) (p) (q)
local notation "I" => dgOdotQuotientInput R d

local notation "Y" => dgSmallPerfectEnvelopeYoneda R (DRaw) (DGSmallPerfectBase R (A))
  (dgSmallPerfectEnvelopeExtensionFamily R (A) (DRaw) Empty
    (dgSmallPerfectBaseFamily R (A)) (gRaw))
local notation "M" => dgHomGluingBimodule R (CL) (DR) (DGOdotCorner R d) (pS) (qS)
local notation "zc" => dgSmallPerfectArrowTargetZero R (A) (CRaw) (L)
local notation "hc" => dgSmallPerfectArrowTargetZero_isZero R (A) (CRaw) (L)
local notation "b" => dgOdotInputRightPoint R d

local notation "J" => dgSmallPerfectSquareCornerInclusion R (A) (CRaw) (DRaw) (E)
  (L) (gRaw) (p) (q)

/-- 評価した元の cone 同型は、同じ実作用に対する全 Hom 自然性を持つ。 -/
lemma dgOdotRealizedConeToRight_naturality (x y : DGOdotQuotientEnd R d) :
    (dgOdotRealizedConeRepresentation R d).map x y ≫
      eHomWhiskerLeft (Complex R)
        (ForgetEnrichment.of (Complex R) ((dgOdotRealizedConeRepresentation R d).obj x))
        ((dgOdotCornerRealization R d).onClosed.map (dgOdotTargetRightConeIso R d).hom) =
    (dgOdotRealizedRightRepresentation R d).map x y ≫
      eHomWhiskerRight (Complex R)
        ((dgOdotCornerRealization R d).onClosed.map (dgOdotTargetRightConeIso R d).hom)
        (ForgetEnrichment.of (Complex R) ((dgOdotRealizedRightRepresentation R d).obj y)) := by
  apply dgClosedComparison_from_parameter R _ _ (dgOdotRealizedRepresentationComparison R d)
    (fun _ => (dgOdotCornerRealization R d).onClosed.map (dgOdotTargetRightConeIso R d).hom)
    ?_ x y
  intro z
  rw [dgOdotRealizedRepresentationComparison_app]
  rfl

/-- 元の三段 cone 同型は、元の終域 End 比較の自由代表作用に全 Hom 自然。 -/
lemma dgOdotRealizedConePointIso_naturality (x y : DGOdotQuotientEnd R d) :
    (dgOdotRealizedConeRepresentation R d).map x y ≫
      eHomWhiskerLeft (Complex R)
        (ForgetEnrichment.of (Complex R) ((dgOdotRealizedConeRepresentation R d).obj x))
        (dgOdotRealizedConePointIso R d).hom =
    (dgOdotRawTargetRepresentation R d).map x y ≫
      eHomWhiskerRight (Complex R) (dgOdotRealizedConePointIso R d).hom
        (ForgetEnrichment.of (Complex R) ((dgOdotRawTargetRepresentation R d).obj y)) := by
  change _ ≫ eHomWhiskerLeft (Complex R) _
    ((dgOdotCornerRealization R d).onClosed.map (dgOdotTargetRightConeIso R d).hom ≫
      (dgOdotRealizedRightPointIso R d).hom) =
    _ ≫ eHomWhiskerRight (Complex R)
      ((dgOdotCornerRealization R d).onClosed.map (dgOdotTargetRightConeIso R d).hom ≫
        (dgOdotRealizedRightPointIso R d).hom) _
  exact dgClosedComparison_comp (Complex R) (C := ModuleCategory R (E))
    ((dgOdotCornerRealization R d).onClosed.map (dgOdotTargetRightConeIso R d).hom)
    ((dgOdotCornerRealization R d).onClosed.map (dgOdotTargetRightConeIso R d).hom)
    (dgOdotRealizedRightPointIso R d).hom (dgOdotRealizedRightPointIso R d).hom
    ((dgOdotRealizedConeRepresentation R d).map x y)
    ((dgOdotRealizedRightRepresentation R d).map x y) ((dgOdotRawTargetRepresentation R d).map x y)
    (dgOdotRealizedConeToRight_naturality R d x y)
    (dgOdotRealizedRightPointIso_naturality R d x y)

/-- 同じ元の三段 cone 同型を成分に持つ、終域 End 表現への全次数自然比較。 -/
def dgOdotRawConeRepresentationComparison :=
  dgFunctorClosedComparison R (dgOdotRealizedConeRepresentation R d)
    (dgOdotRawTargetRepresentation R d) (fun _ => (dgOdotRealizedConePointIso R d).hom)
    (dgOdotRealizedConePointIso_naturality R d)

/-- 同じ元の三段 cone 同型の逆を成分に持つ、全次数自然比較。 -/
def dgOdotRawConeRepresentationInverseComparison :=
  dgFunctorClosedInverseComparison R (dgOdotRealizedConeRepresentation R d)
    (dgOdotRawTargetRepresentation R d) (fun _ => dgOdotRealizedConePointIso R d)
    (dgOdotRealizedConePointIso_naturality R d)

/-- 同じ三段 cone 同型を成分とする、元の閉零表現の実自然同型。 -/
def dgOdotRawConeRepresentationClosedIso :
    (dgOdotRealizedConeRepresentation R d).onClosed ≅
      (dgOdotRawTargetRepresentation R d).onClosed :=
  dgFunctorClosedComparisonIso R _ _ (fun _ => dgOdotRealizedConePointIso R d)
    (dgOdotRealizedConePointIso_naturality R d)

/-- 同じ自然同型の成分は、元の三段対象同型の順射そのもの。 -/
lemma dgOdotRawConeRepresentationClosedIso_hom_app
    (x : ClosedCategory R (DGOdotQuotientEnd R d)) :
    (dgOdotRawConeRepresentationClosedIso R d).hom.app x =
      (dgOdotRealizedConePointIso R d).hom := rfl

end SerrePositivity.KST.SConstruction
