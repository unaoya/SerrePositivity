module
public import SerrePositivity.KST.SConstruction.DGOdotTargetRightBase
public import SerrePositivity.KST.SConstruction.DGPerfectImageEndComparison
public import SerrePositivity.KST.SConstruction.DGExtensionRepresentableEnd

/-! # 同じ指定商 End から元の終域 dg 対象 End への比較
概要：元の右像の代表延長同型を通し、同じ指定商 End を元の終域対象 End に送る。
方針：元の小終域の包含と、同じ代表延長の閉同型による End 比較を合成する。
規約：元の右代表と実延長を保持。使われ方：具体的 ⊙ から元の終域代数への比較。
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

/-- 元の右像の実加群と、元の終域対象の代表加群との同じ代表延長同型。 -/
def dgOdotRightImageRepresentableIso :
    ForgetEnrichment.of (Complex R) ((J).obj ((qS).obj (I).rightPoint)).val ≅
      ForgetEnrichment.of (Complex R) (representable R ((q).obj (b))) :=
  dgModuleExtensionRepresentableIso R (DRaw) (E) (q) (b)

/-- 元の小終域内の右像 End から、元の生の終域対象 End への実比較。 -/
def dgOdotRightImageToCornerEnd :
    DGFunctor R (EndomorphismObject ((qS).obj (I).rightPoint))
      (EndomorphismObject ((q).obj (b))) :=
  dgPerfectImageEndIsoFunctor R (E) (J) ((qS).obj (I).rightPoint) ((q).obj (b))
    (dgOdotRightImageRepresentableIso R d)

/-- 同じ実比較の全 Hom 作用は、型を固定した同じ perfect 像 End 比較。 -/
def dgOdotRightImageToCornerHom :=
  dgPerfectImageEndIsoHom R (E) (J) ((qS).obj (I).rightPoint) ((q).obj (b))
    (dgOdotRightImageRepresentableIso R d)

/-- 同じ右像 End 比較の全 Hom 作用を回収する。 -/
lemma dgOdotRightImageToCornerEnd_map (x y : EndomorphismObject ((qS).obj (I).rightPoint)) :
    (dgOdotRightImageToCornerEnd R d).map x y = dgOdotRightImageToCornerHom R d :=
  dgPerfectImageEndIsoFunctor_map R (E) (J) ((qS).obj (I).rightPoint) ((q).obj (b))
    (dgOdotRightImageRepresentableIso R d) x y

/-- 同じ指定商 End から、元の終域対象の全 End への実 dg 比較射。 -/
def dgOdotTargetCornerEndMap :
    DGFunctor R (DGOdotQuotientEnd R d) (EndomorphismObject ((q).obj (b))) :=
  (dgOdotTargetRightEndMap R d).comp (dgOdotRightImageToCornerEnd R d)

/-- 同じ商 End 比較は元の右像 End 比較と同じ Hom 写像の合成。 -/
lemma dgOdotTargetCornerEndMap_map (x y : DGOdotQuotientEnd R d) :
    (dgOdotTargetCornerEndMap R d).map x y =
      (dgOdotTargetRightEndMap R d).map x y ≫ dgOdotRightImageToCornerHom R d := by
  change _ ≫ (dgOdotRightImageToCornerEnd R d).map _ _ = _
  exact congrArg (fun f => (dgOdotTargetRightEndMap R d).map x y ≫ f)
    (dgOdotRightImageToCornerEnd_map R d _ _)

end SerrePositivity.KST.SConstruction
