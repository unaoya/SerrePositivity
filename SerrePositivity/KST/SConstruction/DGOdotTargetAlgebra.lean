module
public import SerrePositivity.KST.SConstruction.DGOdotTargetCornerRecovery
public import SerrePositivity.KST.SConstruction.DGOdotAlgebra

/-! # 元の実 ⊙ 代数から元の終域代数への比較
概要：同じ指定商 End 比較を右加群の向きで代数化し、元の終域への射を作る。
方針：Sp の既存 End 代数射と、元の一対象圏 End との同じ向きの同型を使う。
規約：元の右代数射の合成を保持。使われ方：具体的 Land–Tamme 比較四角形の右上辺。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
private lemma map_of_eq {R : Type*} [CommRing R]
    {B C : Type*} [DGCategory R B] [DGCategory R C]
    (F G : DGFunctor R B C) (h : F = G) (ho : ∀ x, F.obj x = G.obj x) (x y : B) :
    F.map x y ≫ eqToHom (congrArg₂ (homObject R C) (ho x) (ho y)) = G.map x y := by
  cases h
  simp only [eqToHom_refl, Category.comp_id]

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

/-- 元の実商 End の ⊙ 代数から、元の終域代数への同じ実比較射。 -/
def dgOdotTargetMap : dgOdotAlgebra R d ⟶ d.corner :=
  LocalizingInvariants.dgEndAlgebraMap R (DGOdotQuotientEnd R d)ᵒᵖ
    (dgOdotTargetCornerEndMap R d).op (Opposite.op EndomorphismObject.point) ≫
      (dgAlgebraRightEndIso R d.corner ((q).obj (b))).inv

/-- 同じ比較代数射の基礎鎖写像は、元の指定商 End 比較の全 Hom 作用。 -/
lemma dgOdotTargetMap_hom : (dgOdotTargetMap R d).hom =
    (dgOdotTargetCornerEndMap R d).map EndomorphismObject.point EndomorphismObject.point := by
  change _ ≫ 𝟙 _ = _
  exact Category.comp_id _

/-- 元の右代数から ⊙ を経由する比較は、元の四角形の右辺の代数射を厳密に回収する。 -/
lemma dgOdotTargetMap_right :
    dgOdotRightMap R d ≫ dgOdotTargetMap R d = d.upper := by
  apply Mon.Hom.ext
  change (dgOdotRightMap R d).hom ≫ (dgOdotTargetMap R d).hom = d.upper.hom
  rw [dgOdotRightMap_hom, dgOdotTargetMap_hom]
  have h := map_of_eq
    ((dgOdotRightEndMap R d).comp (dgOdotTargetCornerEndMap R d))
    (endomorphismMap R (q) (b)) (dgOdotTargetCornerEndMap_right R d) (fun _ => rfl)
    EndomorphismObject.point EndomorphismObject.point
  change ((_ ≫ _) ≫ eqToHom (by rfl)) = (q).map (b) (b) at h
  rw [eqToHom_refl, Category.comp_id] at h
  exact h

end SerrePositivity.KST.SConstruction
