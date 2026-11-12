module
public import SerrePositivity.KST.SConstruction.DGOdotTargetQuotient
public import SerrePositivity.KST.SConstruction.DGOdotTargetRightCone
public import SerrePositivity.KST.SConstruction.DGPerfectEndIsoComparison

/-! # 同じ指定商 End から元の右像 End への実 dg 比較
概要：元の右 cone の閉同型と Yoneda の全 Hom 逆同型を通して、元の右像 End へ戻す。
方針：構成済みの実商 End 射を、元の前後合成・元の Yoneda 同型と合成する。
規約：商・局所化の API を新設しない。使われ方：dg ⊙ から元の終域への比較。
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
local notation "G" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R (DGOdotInput.side d)
local notation "p" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R (DGOdotInput.lower d)
local notation "q" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R (DGOdotInput.upper d)
local notation "CL" => DGSmallPerfectArrowTarget R (A) (C) (L)
local notation "DR" => DGSmallPerfectArrowTarget R (A) (DRaw) (G)
local notation "pS" => dgSmallPerfectSquareLeftMap R (A) (C) (DRaw) (E) (L) (G) (p) (q)
local notation "qS" => dgSmallPerfectSquareRightMap R (A) (C) (DRaw) (E) (L) (G) (p) (q)
local notation "I" => dgOdotQuotientInput R d

/-- 同じ右 cone の End を、元の右像の代表加群の End に送る実 dg 共役。 -/
def dgOdotTargetConeEndToRightModuleEnd :
    DGFunctor R (EndomorphismObject (dgOdotTargetCone R d (I).point))
      (EndomorphismObject (representable R ((qS).obj (I).rightPoint))) :=
  dgPerfectEndIsoModuleFunctor R (DGOdotCorner R d) (dgOdotTargetCone R d (I).point)
    ((qS).obj (I).rightPoint) (dgOdotTargetRightConeIso R d)

/-- 同じ右 cone の全 End から元の右像 End への、型を固定した実 Hom 比較。 -/
def dgOdotTargetRightEndHom :=
  dgPerfectEndIsoObjectHom R (DGOdotCorner R d) (dgOdotTargetCone R d (I).point)
    ((qS).obj (I).rightPoint) (dgOdotTargetRightConeIso R d)

/-- 元の指定商 End から、元の小さい終域内の同じ右像 End への実 dg 射。 -/
def dgOdotTargetRightEndMap :
    DGFunctor R (DGOdotQuotientEnd R d) (EndomorphismObject ((qS).obj (I).rightPoint)) :=
  (dgOdotTargetQuotientEndMap R d).comp
    (dgPerfectEndIsoObjectFunctor R (DGOdotCorner R d) (dgOdotTargetCone R d (I).point)
      ((qS).obj (I).rightPoint) (dgOdotTargetRightConeIso R d))

/-- 同じ比較の全 Hom 作用は、元の path 評価と同じ実 Hom 比較の合成。 -/
lemma dgOdotTargetRightEndMap_map (x y : DGOdotQuotientEnd R d) :
    (dgOdotTargetRightEndMap R d).map x y =
      DGQuotient.quotientEvaluation R (dgOdotTargetContractedFunctor R d)
        (I).point (I).point ≫ dgOdotTargetRightEndHom R d := by
  change (dgOdotTargetQuotientEndMap R d).map x y ≫
    (dgPerfectEndIsoObjectFunctor R (DGOdotCorner R d) (dgOdotTargetCone R d (I).point)
      ((qS).obj (I).rightPoint) (dgOdotTargetRightConeIso R d)).map _ _ = _
  exact congrArg₂ (fun f g => f ≫ g) (dgOdotTargetQuotientEndMap_map R d x y)
    (dgPerfectEndIsoObjectFunctor_map R (DGOdotCorner R d)
      (dgOdotTargetCone R d (I).point) ((qS).obj (I).rightPoint)
      (dgOdotTargetRightConeIso R d) _ _)

/-- 同じ比較は元の商 End 単位射から、元の実 cone 関手の End 作用を回収する。 -/
lemma dgOdotTargetRightEndMap_original :
    (I).endUnitMap.comp (dgOdotTargetRightEndMap R d) =
      (endomorphismMap R (dgOdotTargetFunctor R d) (I).point).comp
        (dgPerfectEndIsoObjectFunctor R (DGOdotCorner R d) (dgOdotTargetCone R d (I).point)
          ((qS).obj (I).rightPoint) (dgOdotTargetRightConeIso R d)) := by
  exact (strictDGFunctor_comp_assoc (I).endUnitMap (dgOdotTargetQuotientEndMap R d)
    (dgPerfectEndIsoObjectFunctor R (DGOdotCorner R d) (dgOdotTargetCone R d (I).point)
      ((qS).obj (I).rightPoint) (dgOdotTargetRightConeIso R d))).symm.trans
      (congrArg (fun F => F.comp
        (dgPerfectEndIsoObjectFunctor R (DGOdotCorner R d) (dgOdotTargetCone R d (I).point)
          ((qS).obj (I).rightPoint) (dgOdotTargetRightConeIso R d)))
        (dgOdotTargetQuotientEndMap_original R d))

end SerrePositivity.KST.SConstruction
