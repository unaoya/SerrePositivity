module
public import SerrePositivity.KST.SConstruction.DGOdotTargetRightEnd
public import SerrePositivity.KST.SConstruction.DGHomGluingRightConeHom

/-! # 元の gluing End 射を保つ右像 End 比較
概要：元の零長 path 包含からの比較が、元の右 Hom 射影の像と厳密に一致する。
方針：D β3 の元の射の回収と、同じ右 cone の共役・Yoneda 逆律を合成する。
規約：同じ対象と同じ射を保持。使われ方：元の右代数射との可換性。
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

/-- 同じ指定商 End 比較の元の零長 path への制限は、元の右射影と qS の像。 -/
lemma dgOdotTargetRightEndMap_originalHom (x y : DGOdotQuotientEnd R d) :
    DGQuotient.originalHomInclusion R (DGOdotGluing R d)
        (dgQuotientImage R (I).diagonal) (I).point (I).point ≫
      (dgOdotTargetRightEndMap R d).map x y =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightHomMap R (CL) (DR)
      (dgHomGluingBimodule R (CL) (DR) (DGOdotCorner R d) (pS) (qS)) (I).point (I).point ≫
        (qS).map (I).rightPoint (I).rightPoint := by
  have hQ := DGQuotient.quotientEvaluation_original R
    (dgOdotTargetContractedFunctor R d) (I).point (I).point
  change DGQuotient.originalHomInclusion R (DGOdotGluing R d)
      (dgQuotientImage R (I).diagonal) (I).point (I).point ≫
      DGQuotient.quotientEvaluation R (dgOdotTargetContractedFunctor R d)
        (I).point (I).point =
    dgHomGluingConeHomMap R (CL) (DR) (DGOdotCorner R d) (pS) (qS) (I).point (I).point at hQ
  have hO := dgHomGluingRightConeHom_object R (DGOdotCorner R d) (CL) (DR) (pS) (qS)
    (dgSmallPerfectArrowTargetZero R (A) (C) (L))
    (dgSmallPerfectArrowTargetZero_isZero R (A) (C) (L)) (I).rightPoint
  rw [dgOdotTargetRightEndMap_map]
  erw [← Category.assoc, hQ]
  exact hO

end SerrePositivity.KST.SConstruction
