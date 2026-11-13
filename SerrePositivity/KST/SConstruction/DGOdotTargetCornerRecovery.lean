module
public import SerrePositivity.KST.SConstruction.DGOdotTargetCornerEnd

/-! # 元の右射を保つ指定商 End の終域比較
概要：同じ指定商 End 比較を元の右 End 射と合成すると、元の右辺 dg 射を回収する。
方針：同じ代表延長の全 Hom 回収と、構成済みの元の右像 End の可換式を使う。
規約：元の右始域・元の終域対象を保持。使われ方：⊙ 比較を代数化する右脚の可換性。
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

/-- 元の右像への全 Hom 作用と同じ End 比較の合成は、元の q の Hom 作用。 -/
lemma dgOdotRightImageToCornerHom_recovery :
    ((Y).map (b) (b) ≫ (qS).map (I).rightPoint (I).rightPoint) ≫
      dgOdotRightImageToCornerHom R d = (q).map (b) (b) := by
  change ((yonedaHom R (DRaw) (b) (b) ≫ (dgModuleExtension R (DRaw) (E) (q)).map
      (representable R (b)) (representable R (b))) ≫
        dgEndIsoHom R (D := RightModule R (E))
          (dgModuleExtensionRepresentableIso R (DRaw) (E) (q) (b))) ≫
            (dgYonedaIso R ((q).obj (b)) (representable R ((q).obj (b)))).hom = _
  exact dgExtensionRepresentableEnd_inverseYoneda R (DRaw) (E) (q) (b)

/-- 同じ右像 End 比較は、元の右像関手を元の生の右辺 dg 関手へ戻す。 -/
lemma dgOdotRightImageToCornerEnd_right :
    (endomorphismMap R (dgOdotRightImageFunctor R d) (b)).comp
      (dgOdotRightImageToCornerEnd R d) = endomorphismMap R (q) (b) := by
  apply EnrichedFunctor.ext (Complex R)
    (F := (endomorphismMap R (dgOdotRightImageFunctor R d) (b)).comp
      (dgOdotRightImageToCornerEnd R d))
    (G := endomorphismMap R (q) (b)) (fun _ => rfl)
  intro x y
  change (((Y).map (b) (b) ≫ (qS).map (I).rightPoint (I).rightPoint) ≫
    (dgOdotRightImageToCornerEnd R d).map _ _) ≫ eqToHom (by rfl) = (q).map (b) (b)
  rw [eqToHom_refl, Category.comp_id]
  erw [dgOdotRightImageToCornerEnd_map R d]
  exact dgOdotRightImageToCornerHom_recovery R d

/-- 元の右 End 射を経由する同じ商 End 比較は、元の四角形の右辺の全 End 作用。 -/
lemma dgOdotTargetCornerEndMap_right :
    (dgOdotRightEndMap R d).comp (dgOdotTargetCornerEndMap R d) =
      endomorphismMap R (q) (b) := by
  exact ((strictDGFunctor_comp_assoc (dgOdotRightEndMap R d)
    (dgOdotTargetRightEndMap R d) (dgOdotRightImageToCornerEnd R d)).symm.trans
      (congrArg (fun F => F.comp (dgOdotRightImageToCornerEnd R d))
        (dgOdotTargetRightEndMap_right R d))).trans (dgOdotRightImageToCornerEnd_right R d)

end SerrePositivity.KST.SConstruction
