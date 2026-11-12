module
public import SerrePositivity.KST.SConstruction.DGOdotTargetRightRecovery

/-! # 元の右代数 End 射を保持する終域比較
概要：元の右 End から商 End を経由する射が、元の右像への実延長と一致する。
方針：元の厳密 Yoneda・右軸・零長 path と、構成済みの回収式を合成する。
規約：始域の元の右対象を保持。使われ方：具体的 ⊙ 比較の右脚の可換性。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
private lemma right_recovery {V : Type*} [Category V] {a b c d e : V}
    (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (k : d ⟶ e)
    (p : c ⟶ b) (q : b ⟶ e) (hg : g ≫ p = 𝟙 b) (hk : h ≫ k = p ≫ q) :
    (f ≫ (g ≫ h)) ≫ k = f ≫ q := by
  rw [Category.assoc, Category.assoc, hk, ← Category.assoc g, hg, Category.id_comp]

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

/-- 元の右 dg 圏から元の小終域への、厳密 Yoneda と実延長の合成。 -/
def dgOdotRightImageFunctor : DGFunctor R (DRaw) (DGOdotCorner R d) := (Y).comp (qS)

/-- 同じ右像関手は、元の指定右対象の像を厳密に保持する。 -/
lemma dgOdotRightImageFunctor_obj :
    (dgOdotRightImageFunctor R d).obj (b) = (qS).obj (I).rightPoint := rfl

/-- 元の右 End 射と商 End 比較の合成は、元の右像関手の全 End 作用。 -/
lemma dgOdotTargetRightEndMap_right :
    (dgOdotRightEndMap R d).comp (dgOdotTargetRightEndMap R d) =
      endomorphismMap R (dgOdotRightImageFunctor R d) (b) := by
  apply EnrichedFunctor.ext (Complex R)
    (F := (dgOdotRightEndMap R d).comp (dgOdotTargetRightEndMap R d))
    (G := endomorphismMap R (dgOdotRightImageFunctor R d) (b)) (fun _ => rfl)
  intro x y
  change (((Y).map (b) (b) ≫
    (dgGluingRightQuotientEndMap R (CL) (DR) (M) (zc) (hc)
      (I).diagonal (I).rightPoint).map _ _) ≫
      (dgOdotTargetRightEndMap R d).map _ _) ≫ eqToHom (by rfl) =
        (Y).map (b) (b) ≫ (qS).map (I).rightPoint (I).rightPoint
  rw [eqToHom_refl, Category.comp_id]
  erw [dgGluingRightQuotientEndMap_map R (CL) (DR) (M) (zc) (hc)
    (I).diagonal (I).rightPoint]
  let i := dgGluingRightAxisHomIso R (CL) (DR) (M) (zc) (hc)
    (I).rightPoint (I).rightPoint
  have hi : i.inv ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightHomMap R (CL) (DR) (M) (I).point (I).point = 𝟙 _ :=
    (congrArg (fun f => i.inv ≫ f)
      (dgGluingRightAxisHomIso_hom R (CL) (DR) (M) (zc) (hc)
        (I).rightPoint (I).rightPoint).symm).trans i.inv_hom_id
  exact right_recovery _ _ _ _ _ _ hi
    (dgOdotTargetRightEndMap_originalHom R d _ _)

end SerrePositivity.KST.SConstruction
