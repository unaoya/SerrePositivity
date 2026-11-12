module
public import SerrePositivity.KST.SConstruction.DGOdotTargetSmallPerfect

/-! # 同じ小さい実 Perf 模型における cone 作用の全 Hom 比較
概要：元の全 Hom 比較を、同じ cone 点と自由代表を含む実小模型へ持ち上げる。
方針：充満部分圏の前後合成の回収式で、元の三段同型の自然性を保持する。
規約：対象と全次数成分を変更しない。使われ方：元の比較射の一回 Perf 延長への入力。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "A" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R (DGOdotInput.source d)
local notation "CRaw" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R (DGOdotInput.left d)
local notation "DRaw" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R (DGOdotInput.right d)
local notation "E" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R (DGOdotInput.corner d)
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

/-- 同じ小模型の cone 作用は、元の評価済み cone の全 Hom 作用を保つ。 -/
lemma dgOdotConeSmallRepresentation_map (x y : DGOdotQuotientEnd R d) :
    (dgOdotConeSmallRepresentation R d).map x y =
      (dgOdotRealizedConeRepresentation R d).map x y := rfl

/-- 同じ小模型の自由代表作用は、元の終域 End 比較の全 Hom 作用を保つ。 -/
lemma dgOdotTargetSmallRepresentation_map (x y : DGOdotQuotientEnd R d) :
    (dgOdotTargetSmallRepresentation R d).map x y =
      (dgOdotRawTargetRepresentation R d).map x y := rfl

/-- 同じ小模型の比較順射の全 Hom 後合成は、元の実加群上の後合成。 -/
lemma dgOdotTargetSmallPointIso_whiskerLeft :
    eHomWhiskerLeft (Complex R)
      (ForgetEnrichment.of (Complex R) (dgOdotTargetSmallConePoint R d))
      (dgOdotTargetSmallPointIso R d).hom =
    eHomWhiskerLeft (Complex R)
      (ForgetEnrichment.of (Complex R) ((dgOdotCornerRealization R d).obj
        (dgOdotTargetCone R d (I).point).val)) (dgOdotRealizedConePointIso R d).hom := by
  exact (dgFullClosedIsoLift_whiskerLeft R (PerfectDGModule R (E))
    (dgSmallPerfectEnvelopeObjects R (E) PUnit.{1} (dgOdotTargetConeFamily R d))
    (dgOdotTargetSmallConePoint R d) (dgOdotTargetSmallRepresentablePoint R d)
    (dgOdotRealizedConePerfectPointIso R d) (dgOdotTargetSmallConePoint R d)).trans
      (dgPerfectClosedIsoLift_whiskerLeft R (E) (dgOdotRealizedConePerfectPoint R d)
        (dgRepresentablePerfectPoint R (E) ((q).obj (b))) (dgOdotRealizedConePerfectPoint R d)
        (dgOdotRealizedConePointIso R d))

/-- 同じ小模型の比較順射の全 Hom 前合成も、元の実加群上の前合成。 -/
lemma dgOdotTargetSmallPointIso_whiskerRight :
    eHomWhiskerRight (Complex R) (dgOdotTargetSmallPointIso R d).hom
      (ForgetEnrichment.of (Complex R) (dgOdotTargetSmallRepresentablePoint R d)) =
    eHomWhiskerRight (Complex R) (dgOdotRealizedConePointIso R d).hom
      (ForgetEnrichment.of (Complex R) (representable R ((q).obj (b)))) := by
  exact (dgFullClosedIsoLift_whiskerRight R (PerfectDGModule R (E))
    (dgSmallPerfectEnvelopeObjects R (E) PUnit.{1} (dgOdotTargetConeFamily R d))
    (dgOdotTargetSmallConePoint R d) (dgOdotTargetSmallRepresentablePoint R d)
    (dgOdotRealizedConePerfectPointIso R d) (dgOdotTargetSmallRepresentablePoint R d)).trans
      (dgPerfectClosedIsoLift_whiskerRight R (E) (dgOdotRealizedConePerfectPoint R d)
        (dgRepresentablePerfectPoint R (E) ((q).obj (b)))
        (dgRepresentablePerfectPoint R (E) ((q).obj (b))) (dgOdotRealizedConePointIso R d))

/-- 元の三段同型は、同じ小模型でも全 Hom に関して自然。 -/
lemma dgOdotTargetSmallPointIso_naturality (x y : DGOdotQuotientEnd R d) :
    (dgOdotConeSmallRepresentation R d).map x y ≫ eHomWhiskerLeft (Complex R)
      (ForgetEnrichment.of (Complex R) (dgOdotTargetSmallConePoint R d))
      (dgOdotTargetSmallPointIso R d).hom =
    (dgOdotTargetSmallRepresentation R d).map x y ≫ eHomWhiskerRight (Complex R)
      (dgOdotTargetSmallPointIso R d).hom
      (ForgetEnrichment.of (Complex R) (dgOdotTargetSmallRepresentablePoint R d)) := by
  rw [dgOdotConeSmallRepresentation_map, dgOdotTargetSmallRepresentation_map]
  erw [dgOdotTargetSmallPointIso_whiskerLeft, dgOdotTargetSmallPointIso_whiskerRight]
  exact dgOdotRealizedConePointIso_naturality R d x y

/-- 同じ小模型の元の成分を持つ、全次数自然な cone 比較。 -/
def dgOdotSmallConeRepresentationComparison :=
  dgFunctorClosedComparison R (dgOdotConeSmallRepresentation R d)
    (dgOdotTargetSmallRepresentation R d) (fun _ => (dgOdotTargetSmallPointIso R d).hom)
    (dgOdotTargetSmallPointIso_naturality R d)

/-- 同じ元の三段同型の逆を使う、小模型内の全次数逆比較。 -/
def dgOdotSmallConeRepresentationInverseComparison :=
  dgFunctorClosedInverseComparison R (dgOdotConeSmallRepresentation R d)
    (dgOdotTargetSmallRepresentation R d) (fun _ => dgOdotTargetSmallPointIso R d)
    (dgOdotTargetSmallPointIso_naturality R d)

/-- 同じ小模型内の元の閉零表現を、同じ比較成分のまま結ぶ自然同型。 -/
def dgOdotSmallConeRepresentationClosedIso :
    (dgOdotConeSmallRepresentation R d).onClosed ≅
      (dgOdotTargetSmallRepresentation R d).onClosed :=
  dgFunctorClosedComparisonIso R _ _ (fun _ => dgOdotTargetSmallPointIso R d)
    (dgOdotTargetSmallPointIso_naturality R d)

end SerrePositivity.KST.SConstruction
