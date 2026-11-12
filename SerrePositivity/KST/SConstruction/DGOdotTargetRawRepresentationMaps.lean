module
public import SerrePositivity.KST.SConstruction.DGOdotTargetRepresentablePoint

/-! # 元の終域への表現比較で用いる同じ全 Hom 写像
概要：評価した右作用・元の実像作用・元の比較 End の代表作用を元の Hom で表示する。
方針：既存 End 写像の回収と同じ Yoneda 逆律を使う。
規約：全 Hom 写像を変更しない。使われ方：元の自由代表への比較の全次数自然性。
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

/-- 元の指定商 End が、元の実右像加群に作用する中間関手。 -/
def dgOdotRightImageRepresentation :
    DGFunctor R (DGOdotQuotientEnd R d) (RightModule R (E)) :=
  ((dgOdotTargetRightEndMap R d).comp
    (endomorphismInclusion R ((qS).obj (I).rightPoint))).comp
      (dgPerfectRealizationKernel R (DGOdotCorner R d) (E) (J))

/-- 元の終域 End 比較から元の自由代表へ作用する同じ実関手。 -/
def dgOdotRawTargetRepresentation :
    DGFunctor R (DGOdotQuotientEnd R d) (RightModule R (E)) :=
  ((dgOdotTargetCornerEndMap R d).comp (endomorphismInclusion R ((q).obj (b)))).comp
    (dgYoneda R (E))

/-- 中間の実右像作用は、元の右 End 比較と元の包含の Hom 作用の合成。 -/
lemma dgOdotRightImageRepresentation_map (x y : DGOdotQuotientEnd R d) :
    (dgOdotRightImageRepresentation R d).map x y =
      (dgOdotTargetRightEndMap R d).map x y ≫ (J).map
        ((qS).obj (I).rightPoint) ((qS).obj (I).rightPoint) := by
  change (_ ≫ 𝟙 _) ≫ (_ ≫ 𝟙 _) = _
  erw [Category.comp_id, Category.comp_id]

/-- 同じ生の End 比較を元の Yoneda で戻すと、元の実像 End 共役を回収する。 -/
lemma dgOdotRightImageToCornerHom_yoneda :
    dgOdotRightImageToCornerHom R d ≫ yonedaHom R (E) ((q).obj (b)) ((q).obj (b)) =
      (J).map ((qS).obj (I).rightPoint) ((qS).obj (I).rightPoint) ≫
        dgPerfectEndIsoModuleHom R (E) ((J).obj ((qS).obj (I).rightPoint))
          ((q).obj (b)) (dgOdotRightImageRepresentableIso R d) := by
  change (_ ≫ dgPerfectEndIsoObjectHom R (E) ((J).obj ((qS).obj (I).rightPoint))
    ((q).obj (b)) (dgOdotRightImageRepresentableIso R d)) ≫ _ = _
  exact (Category.assoc _ _ _).trans (congrArg (fun f =>
    (J).map ((qS).obj (I).rightPoint) ((qS).obj (I).rightPoint) ≫ f)
      (dgPerfectEndIsoObjectHom_yoneda R (E) ((J).obj ((qS).obj (I).rightPoint))
        ((q).obj (b)) (dgOdotRightImageRepresentableIso R d)))

/-- 元の生の代表作用は、中間の実像作用に同じ閉共役を合成したもの。 -/
lemma dgOdotRawTargetRepresentation_map (x y : DGOdotQuotientEnd R d) :
    (dgOdotRawTargetRepresentation R d).map x y =
      ((dgOdotTargetRightEndMap R d).map x y ≫ (J).map
        ((qS).obj (I).rightPoint) ((qS).obj (I).rightPoint)) ≫
          dgPerfectEndIsoModuleHom R (E) ((J).obj ((qS).obj (I).rightPoint))
            ((q).obj (b)) (dgOdotRightImageRepresentableIso R d) := by
  change ((dgOdotTargetCornerEndMap R d).map x y ≫ 𝟙 _) ≫
    yonedaHom R (E) ((q).obj (b)) ((q).obj (b)) = _
  rw [Category.comp_id, dgOdotTargetCornerEndMap_map]
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun f => (dgOdotTargetRightEndMap R d).map x y ≫ f)
      (dgOdotRightImageToCornerHom_yoneda R d)).trans (Category.assoc _ _ _).symm)

/-- 評価した右代表作用は、元の右 End 比較・元の Yoneda・同じ tensor の Hom 合成。 -/
lemma dgOdotRealizedRightRepresentation_map (x y : DGOdotQuotientEnd R d) :
    (dgOdotRealizedRightRepresentation R d).map x y =
      ((dgOdotTargetRightEndMap R d).map x y ≫
        yonedaHom R (DGOdotCorner R d) ((qS).obj (I).rightPoint) ((qS).obj (I).rightPoint)) ≫
          (dgOdotCornerRealization R d).map (representable R ((qS).obj (I).rightPoint))
            (representable R ((qS).obj (I).rightPoint)) := by
  change (((dgOdotTargetRightEndMap R d).map x y ≫ 𝟙 _) ≫ _) ≫ _ = _
  rw [Category.comp_id]
  rfl

end SerrePositivity.KST.SConstruction
