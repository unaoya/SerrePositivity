module
public import SerrePositivity.KST.SConstruction.DGOdotTargetRealizedRepresentation
public import SerrePositivity.KST.SConstruction.DGOdotTargetCornerEnd

/-! # 元の終域で評価した指定 cone と元の自由代表の同型
概要：同じ tensor 評価・元の右 cone 同型・元の代表延長同型で、元の自由代表へ戻す。
方針：同じ右単位と既存二同型を順に合成し、その元の射を回収する。
規約：本節の終域同型は対象別。使われ方：実比較の元の終域での全 Hom 照合の固定成分。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "A" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R (DGOdotInput.source d)
local notation "C" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R (DGOdotInput.left d)
local notation "DRaw" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R (DGOdotInput.right d)
local notation "E" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R (DGOdotInput.corner d)
local notation "L" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R (DGOdotInput.top d)
local notation "gRaw" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R (DGOdotInput.side d)
local notation "p" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R (DGOdotInput.lower d)
local notation "q" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R (DGOdotInput.upper d)
local notation "CL" => DGSmallPerfectArrowTarget R (A) (C) (L)
local notation "DR" => DGSmallPerfectArrowTarget R (A) (DRaw) (gRaw)
local notation "pS" => dgSmallPerfectSquareLeftMap R (A) (C) (DRaw) (E) (L) (gRaw) (p) (q)
local notation "qS" => dgSmallPerfectSquareRightMap R (A) (C) (DRaw) (E) (L) (gRaw) (p) (q)
local notation "I" => dgOdotQuotientInput R d

local notation "Y" => dgSmallPerfectEnvelopeYoneda R (DRaw) (DGSmallPerfectBase R (A))
  (dgSmallPerfectEnvelopeExtensionFamily R (A) (DRaw) Empty
    (dgSmallPerfectBaseFamily R (A)) (gRaw))
local notation "M" => dgHomGluingBimodule R (CL) (DR) (DGOdotCorner R d) (pS) (qS)
local notation "zc" => dgSmallPerfectArrowTargetZero R (A) (C) (L)
local notation "hc" => dgSmallPerfectArrowTargetZero_isZero R (A) (C) (L)
local notation "b" => dgOdotInputRightPoint R d

local notation "J" => dgSmallPerfectSquareCornerInclusion R (A) (C) (DRaw) (E)
  (L) (gRaw) (p) (q)

/-- 評価した元の右代表加群と、元の終域の自由代表との同じ二段比較。 -/
def dgOdotRealizedRightPointIso :
    ForgetEnrichment.of (Complex R) ((dgOdotCornerRealization R d).obj
      (representable R ((qS).obj (I).rightPoint))) ≅
        ForgetEnrichment.of (Complex R) (representable R ((q).obj (b))) :=
  dgPerfectRealizationRepresentableIso R (DGOdotCorner R d) (E) (J)
    ((qS).obj (I).rightPoint) ≪≫ dgOdotRightImageRepresentableIso R d

/-- 同じ右点比較の順射は、元の右単位評価と元の代表延長同型の順射の合成。 -/
lemma dgOdotRealizedRightPointIso_hom :
    (dgOdotRealizedRightPointIso R d).hom =
      (dgPerfectRealizationRepresentableIso R (DGOdotCorner R d) (E) (J)
        ((qS).obj (I).rightPoint)).hom ≫ (dgOdotRightImageRepresentableIso R d).hom := rfl

/-- 評価した同じ指定 cone と、元の終域の自由代表との元の三段比較。 -/
def dgOdotRealizedConePointIso :
    ForgetEnrichment.of (Complex R) ((dgOdotCornerRealization R d).obj
      (dgOdotTargetCone R d (I).point).val) ≅
        ForgetEnrichment.of (Complex R) (representable R ((q).obj (b))) :=
  (dgOdotCornerRealization R d).onClosed.mapIso (dgOdotTargetRightConeIso R d) ≪≫
    dgOdotRealizedRightPointIso R d

/-- 同じ cone 比較は、元の cone 閉同型の評価と同じ右点比較を保持する。 -/
lemma dgOdotRealizedConePointIso_hom :
    (dgOdotRealizedConePointIso R d).hom =
      (dgOdotCornerRealization R d).onClosed.map (dgOdotTargetRightConeIso R d).hom ≫
        (dgOdotRealizedRightPointIso R d).hom := rfl

end SerrePositivity.KST.SConstruction
