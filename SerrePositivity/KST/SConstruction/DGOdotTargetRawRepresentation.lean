module
public import SerrePositivity.KST.SConstruction.DGOdotTargetRawRepresentationMaps
public import SerrePositivity.KST.SConstruction.DGClosedComparisonComposition

/-! # 元の自由代表への右点比較の全 Hom 自然性
概要：右単位と元の代表延長同型の合成は、元の終域 End 比較の全 Hom 作用に自然。
方針：元の二つの全 Hom 可換式を、中間の実像作用を保持して合成する。
規約：対象別同型から自然性を仮定しない。使われ方：評価した cone と元の比較射の照合。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories

private lemma fourfold {V : Type*} [Category V] {a b c d e f : V}
    (r : a ⟶ b) (s : b ⟶ c) (t : c ⟶ d) (u : d ⟶ e) (m : b ⟶ f) (v : f ⟶ e)
    (h : (s ≫ t) ≫ u = m ≫ v) : ((r ≫ s) ≫ t) ≫ u = (r ≫ m) ≫ v := by
  simpa only [Category.assoc] using congrArg (fun k => r ≫ k) h

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

/-- 元の小終域の右代表を評価する、同じ右単位同型。 -/
def dgOdotRightEvaluationIso :
    ForgetEnrichment.of (Complex R) ((dgOdotCornerRealization R d).obj
      (representable R ((qS).obj (I).rightPoint))) ≅
        ForgetEnrichment.of (Complex R) ((J).obj ((qS).obj (I).rightPoint)).val :=
  dgPerfectRealizationRepresentableIso R (DGOdotCorner R d) (E) (J) ((qS).obj (I).rightPoint)

/-- 同じ右単位同型は、元の商 End の全 Hom 作用に自然。 -/
lemma dgOdotRightEvaluationIso_naturality (x y : DGOdotQuotientEnd R d) :
    (dgOdotRealizedRightRepresentation R d).map x y ≫
      eHomWhiskerLeft (Complex R)
        (ForgetEnrichment.of (Complex R) ((dgOdotRealizedRightRepresentation R d).obj x))
        (dgOdotRightEvaluationIso R d).hom =
    (dgOdotRightImageRepresentation R d).map x y ≫
      eHomWhiskerRight (Complex R) (dgOdotRightEvaluationIso R d).hom
        (ForgetEnrichment.of (Complex R) ((dgOdotRightImageRepresentation R d).obj y)) := by
  rw [dgOdotRealizedRightRepresentation_map, dgOdotRightImageRepresentation_map]
  have h := dgPerfectRealizationRepresentableIso_naturality R (DGOdotCorner R d) (E) (J)
    ((qS).obj (I).rightPoint) ((qS).obj (I).rightPoint)
  change yonedaHom R (DGOdotCorner R d) ((qS).obj (I).rightPoint) ((qS).obj (I).rightPoint) ≫
    (dgOdotCornerRealization R d).map (representable R ((qS).obj (I).rightPoint))
      (representable R ((qS).obj (I).rightPoint)) ≫
      eHomWhiskerLeft (Complex R)
        (ForgetEnrichment.of (Complex R) ((dgOdotRealizedRightRepresentation R d).obj x))
        (dgOdotRightEvaluationIso R d).hom =
    ((J).map ((qS).obj (I).rightPoint) ((qS).obj (I).rightPoint) ≫ 𝟙 _) ≫
      eHomWhiskerRight (Complex R) (dgOdotRightEvaluationIso R d).hom
        (ForgetEnrichment.of (Complex R) ((dgOdotRightImageRepresentation R d).obj y)) at h
  erw [Category.comp_id] at h
  exact fourfold _ _ _ _ _ _ ((Category.assoc _ _ _).trans h)

/-- 同じ代表延長同型は、中間の実像作用と元の終域 End 比較の代表作用を結ぶ。 -/
lemma dgOdotRightImageRepresentation_naturality (x y : DGOdotQuotientEnd R d) :
    (dgOdotRightImageRepresentation R d).map x y ≫
      eHomWhiskerLeft (Complex R)
        (ForgetEnrichment.of (Complex R) ((dgOdotRightImageRepresentation R d).obj x))
        (dgOdotRightImageRepresentableIso R d).hom =
    (dgOdotRawTargetRepresentation R d).map x y ≫
      eHomWhiskerRight (Complex R) (dgOdotRightImageRepresentableIso R d).hom
        (ForgetEnrichment.of (Complex R) ((dgOdotRawTargetRepresentation R d).obj y)) := by
  rw [dgOdotRightImageRepresentation_map, dgOdotRawTargetRepresentation_map]
  exact dgPerfectEndRepresentation_precompose R (E) ((J).obj ((qS).obj (I).rightPoint))
    ((q).obj (b)) (dgOdotRightImageRepresentableIso R d) _

/-- 元の二段右点同型は、元の比較射の全 Hom 表現に関して自然。 -/
lemma dgOdotRealizedRightPointIso_naturality (x y : DGOdotQuotientEnd R d) :
    (dgOdotRealizedRightRepresentation R d).map x y ≫
      eHomWhiskerLeft (Complex R)
        (ForgetEnrichment.of (Complex R) ((dgOdotRealizedRightRepresentation R d).obj x))
        (dgOdotRealizedRightPointIso R d).hom =
    (dgOdotRawTargetRepresentation R d).map x y ≫
      eHomWhiskerRight (Complex R) (dgOdotRealizedRightPointIso R d).hom
        (ForgetEnrichment.of (Complex R) ((dgOdotRawTargetRepresentation R d).obj y)) := by
  change _ ≫ eHomWhiskerLeft (Complex R) _
    ((dgOdotRightEvaluationIso R d).hom ≫ (dgOdotRightImageRepresentableIso R d).hom) =
    _ ≫ eHomWhiskerRight (Complex R)
      ((dgOdotRightEvaluationIso R d).hom ≫ (dgOdotRightImageRepresentableIso R d).hom) _
  exact dgClosedComparison_comp (Complex R) (C := ModuleCategory R (E))
    (dgOdotRightEvaluationIso R d).hom (dgOdotRightEvaluationIso R d).hom
    (dgOdotRightImageRepresentableIso R d).hom (dgOdotRightImageRepresentableIso R d).hom
    ((dgOdotRealizedRightRepresentation R d).map x y)
    ((dgOdotRightImageRepresentation R d).map x y) ((dgOdotRawTargetRepresentation R d).map x y)
    (dgOdotRightEvaluationIso_naturality R d x y)
    (dgOdotRightImageRepresentation_naturality R d x y)

/-- 同じ元の二段右点同型を成分に持つ、全次数自然比較。 -/
def dgOdotRawRightRepresentationComparison :=
  dgFunctorClosedComparison R (dgOdotRealizedRightRepresentation R d)
    (dgOdotRawTargetRepresentation R d) (fun _ => (dgOdotRealizedRightPointIso R d).hom)
    (dgOdotRealizedRightPointIso_naturality R d)

/-- 同じ元の二段右点同型の逆を成分に持つ、全次数自然比較。 -/
def dgOdotRawRightRepresentationInverseComparison :=
  dgFunctorClosedInverseComparison R (dgOdotRealizedRightRepresentation R d)
    (dgOdotRawTargetRepresentation R d) (fun _ => dgOdotRealizedRightPointIso R d)
    (dgOdotRealizedRightPointIso_naturality R d)

/-- 同じ元の二段右点同型の成分を持つ、閉零射圏での実自然同型。 -/
def dgOdotRawRightRepresentationClosedIso :
    (dgOdotRealizedRightRepresentation R d).onClosed ≅
      (dgOdotRawTargetRepresentation R d).onClosed :=
  dgFunctorClosedComparisonIso R _ _ (fun _ => dgOdotRealizedRightPointIso R d)
    (dgOdotRealizedRightPointIso_naturality R d)

end SerrePositivity.KST.SConstruction
