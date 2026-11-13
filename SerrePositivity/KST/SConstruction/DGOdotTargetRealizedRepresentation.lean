module
public import SerrePositivity.KST.SConstruction.DGOdotTargetRepresentation
public import SerrePositivity.KST.SConstruction.DGPerfectRealization
public import SerrePositivity.DifferentialGraded.Functor.DGFunctorHomPostcomposition

/-! # 元の終域へ評価した商 cone と右代表加群の作用
概要：元の小終域の実加群作用を同じ tensor 評価で元の終域へ戻し、元の閉同型を保つ。
方針：元の全次数自然比較を厳密 dg 後合成し、同じ閉零自然同型も写す。
規約：元の cone と同じ tensor を保持。使われ方：実 ⊙ 比較の元の終域での表現照合。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "A" => _root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R (DGOdotInput.source d)
local notation "C" => _root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R (DGOdotInput.left d)
local notation "DRaw" => _root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R (DGOdotInput.right d)
local notation "E" => _root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R (DGOdotInput.corner d)
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

/-- 元の小終域の実加群を、同じ包含の評価双加群で元の終域へ戻す。 -/
def dgOdotCornerRealization :
    DGFunctor R (RightModule R (DGOdotCorner R d)) (RightModule R (E)) :=
  dgPerfectRealization R (DGOdotCorner R d) (E) (J)

/-- 元の商 cone 作用を、同じ実 tensor により元の終域へ評価する。 -/
def dgOdotRealizedConeRepresentation :
    DGFunctor R (DGOdotQuotientEnd R d) (RightModule R (E)) :=
  (dgOdotQuotientConeRepresentation R d).comp (dgOdotCornerRealization R d)

/-- 元の右像の代表作用を、同じ実 tensor により元の終域へ評価する。 -/
def dgOdotRealizedRightRepresentation :
    DGFunctor R (DGOdotQuotientEnd R d) (RightModule R (E)) :=
  (dgOdotQuotientRightRepresentation R d).comp (dgOdotCornerRealization R d)

/-- 同じ tensor 評価後も、元の全次数自然比較を保持する。 -/
def dgOdotRealizedRepresentationComparison :=
  dgFunctorParamPost R (DGOdotQuotientEnd R d) (RightModule R (DGOdotCorner R d))
    (RightModule R (E)) (dgOdotCornerRealization R d)
    (dgOdotQuotientRepresentationComparison R d)

/-- 同じ tensor 評価後の、元の閉同型の逆から得る全次数自然比較。 -/
def dgOdotRealizedRepresentationInverseComparison :=
  dgFunctorParamPost R (DGOdotQuotientEnd R d) (RightModule R (DGOdotCorner R d))
    (RightModule R (E)) (dgOdotCornerRealization R d)
    (dgOdotQuotientRepresentationInverseComparison R d)

/-- 同じ元の閉零自然同型を同じ tensor 評価へ写した実自然同型。 -/
def dgOdotRealizedRepresentationClosedIso :
    (dgOdotRealizedConeRepresentation R d).onClosed ≅
      (dgOdotRealizedRightRepresentation R d).onClosed :=
  EnrichedFunctor.forgetComp (dgOdotQuotientConeRepresentation R d) (dgOdotCornerRealization R d) ≪≫
    Functor.isoWhiskerRight (dgOdotQuotientRepresentationClosedIso R d)
      (dgOdotCornerRealization R d).onClosed ≪≫
        (EnrichedFunctor.forgetComp (dgOdotQuotientRightRepresentation R d)
          (dgOdotCornerRealization R d)).symm

/-- 同じ閉零自然同型の成分は、元の右 cone 同型の同じ tensor 評価。 -/
lemma dgOdotRealizedRepresentationClosedIso_hom_app
    (x : ClosedCategory R (DGOdotQuotientEnd R d)) :
    (dgOdotRealizedRepresentationClosedIso R d).hom.app x =
      (dgOdotCornerRealization R d).onClosed.map (dgOdotTargetRightConeIso R d).hom := by
  change 𝟙 _ ≫ ((dgOdotCornerRealization R d).onClosed.map
    (dgOdotTargetRightConeIso R d).hom ≫ 𝟙 _) = _
  rw [Category.id_comp, Category.comp_id]

/-- 全次数比較の成分も、同じ元の閉同型の全 Hom 写像による像。 -/
lemma dgOdotRealizedRepresentationComparison_app (x : DGOdotQuotientEnd R d) :
    (dgOdotRealizedRepresentationComparison R d).app x =
      ForgetEnrichment.homTo (Complex R) (dgOdotTargetRightConeIso R d).hom ≫
        (dgOdotCornerRealization R d).map
          (dgOdotTargetCone R d (I).point).val
          (representable R ((qS).obj (I).rightPoint)) := rfl

end SerrePositivity.KST.SConstruction
