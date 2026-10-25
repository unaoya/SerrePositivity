module
public import SerrePositivity.InfinityCategories.Derived.Gluing.MilnorFreeHomTransport
/-!
概要：実自由 Hom の cocone 同型の左右射影と第三 cochain を回収する。
方針：同じ正方形から作った cocone 写像の公開成分式を適用する。
規約：比較差の可換式だけを入力とし、対角作用の一致は別に検証する。
使われ方：実自由対角の全 Hom 作用を三成分一意性で照合する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits CochainComplex HomComplex DifferentialGraded KST.SConstruction
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "A" => dgAlgebraCategory R d.source
local notation "C" => dgAlgebraCategory R d.left
local notation "D" => dgAlgebraCategory R d.right
local notation "E" => dgAlgebraCategory R d.corner
local notation "L" => dgAlgebraMap R d.top
local notation "G" => dgAlgebraMap R d.side
local notation "p" => dgAlgebraMap R d.lower
local notation "q" => dgAlgebraMap R d.upper
local notation "CL" => DGSmallPerfectArrowTarget R (A) (C) (L)
local notation "DR" => DGSmallPerfectArrowTarget R (A) (D) (G)
local notation "V" => DGSmallPerfectSquareCorner R (A) (C) (D) (E) (L) (G) (p) (q)
local notation "pS" => dgSmallPerfectSquareLeftMap R (A) (C) (D) (E) (L) (G) (p) (q)
local notation "qS" => dgSmallPerfectSquareRightMap R (A) (C) (D) (E) (L) (G) (p) (q)
local notation "M" => dgHomGluingBimodule R (CL) (DR) (V) (pS) (qS)
local notation "N" => dgHomGluingBimodule R (C) (D) (E) (p) (q)
local notation "X" => dgGluingMilnorActualFreeObject R d
local notation "Y" => dgGluingMilnorGenerator R d
variable (h : dgGluingMilnorActualFreeDifference R d ≫
    (dgGluingMilnorFreeCoefficientHomIso R d).hom =
    (dgGluingMilnorFreePairHomIso R d).hom ≫ dgGluingMilnorRawFreeDifference R d)
lemma dgGluingMilnorFreeHomIso_left :
    (dgGluingMilnorFreeHomIso R d h).hom ≫ dgGluingLeftHomMap R (C) (D) (N) (Y) (Y) =
      dgGluingLeftHomMap R (CL) (DR) (M) (X) (X) ≫
        (dgGluingMilnorFreeLeftHomIso R d).hom := by
  change complexMappingCoconeMap (dgGluingMilnorActualFreeDifference R d)
    (dgGluingMilnorRawFreeDifference R d) (dgGluingMilnorFreePairHomIso R d).hom
    (dgGluingMilnorFreeCoefficientHomIso R d).hom h ≫
    (CochainComplex.mappingCocone.fst _ ≫ biprod.fst) = _
  rw [← Category.assoc, complexMappingCoconeMap_fst, Category.assoc]
  simp only [dgGluingMilnorFreePairHomIso, biprod.mapIso_hom, biprod.map_fst]
  rfl
lemma dgGluingMilnorFreeHomIso_right :
    (dgGluingMilnorFreeHomIso R d h).hom ≫ dgGluingRightHomMap R (C) (D) (N) (Y) (Y) =
      dgGluingRightHomMap R (CL) (DR) (M) (X) (X) ≫
        (dgGluingMilnorFreeRightHomIso R d).hom := by
  change complexMappingCoconeMap (dgGluingMilnorActualFreeDifference R d)
    (dgGluingMilnorRawFreeDifference R d) (dgGluingMilnorFreePairHomIso R d).hom
    (dgGluingMilnorFreeCoefficientHomIso R d).hom h ≫
    (CochainComplex.mappingCocone.fst _ ≫ biprod.snd) = _
  rw [← Category.assoc, complexMappingCoconeMap_fst, Category.assoc]
  simp only [dgGluingMilnorFreePairHomIso, biprod.mapIso_hom, biprod.map_snd]
  rfl
lemma dgGluingMilnorFreeHomIso_comparison (K : Complex R)
    (f : K ⟶ homObject R (DGOdotGluing R d) (X) (X)) :
    dgGluingHomComparison R (C) (D) (N) (Y) (Y) K
      (f ≫ (dgGluingMilnorFreeHomIso R d h).hom) =
    (dgGluingHomComparison R (CL) (DR) (M) (X) (X) K f).comp
      (Cochain.ofHom (dgGluingMilnorFreeCoefficientHomIso R d).hom) (add_zero (-1)) := by
  apply Cochain.ext
  intro i j hij
  simp only [dgGluingHomComparison, dgGluingHomPrimitive, Cochain.comp_zero_cochain_v,
    Cochain.zero_cochain_comp_v, Cochain.ofHom_v, HomologicalComplex.comp_f]
  have he := congrArg (fun t => f.f i ≫ t)
    (complexMappingCoconeMap_f_snd_v (dgGluingMilnorActualFreeDifference R d)
    (dgGluingMilnorRawFreeDifference R d) (dgGluingMilnorFreePairHomIso R d).hom
    (dgGluingMilnorFreeCoefficientHomIso R d).hom h i j hij)
  simpa only [dgGluingMilnorFreeHomIso, complexMappingCoconeMapIso, Category.assoc] using he
end SerrePositivity.InfinityCategories
