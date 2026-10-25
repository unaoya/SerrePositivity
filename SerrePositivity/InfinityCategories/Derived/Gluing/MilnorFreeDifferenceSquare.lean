module
public import SerrePositivity.InfinityCategories.Derived.Gluing.MilnorFreeProjectedHomAction
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetCommaHom
public import SerrePositivity.InfinityCategories.Derived.Gluing.MilnorFreeDiagonalComparison
/-!
概要：元自由 End の比較差を Milnor fiber の比較差へ送る。
方針：左右作用の共役と射影評価を合わせ、直和の二成分で比較する。
規約：元対角・固定した自由 Hom 同型・比較差の符号を保持する。
使われ方：Milnor 条件から元の小 Perf 対角の全 Hom 準同型性を得る。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded KST.SConstruction
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
local notation "LS" => dgSmallPerfectArrow R (A) (C) (L)
local notation "GS" => dgSmallPerfectArrow R (A) (D) (G)
local notation "b" => dgGluingMilnorSourceGenerator R d
local notation "X" => dgGluingMilnorActualFreeObject R d
local notation "Y" => dgGluingMilnorGenerator R d
lemma dgGluingMilnorFreeLeftAction_evaluate :
    dgGluingLeftAction R (CL) (DR) (M) (X) (X) ≫
        (dgGluingMilnorFreeCoefficientHomIso R d).hom =
      (dgGluingMilnorFreeLeftHomIso R d).hom ≫
        dgGluingLeftAction R (C) (D)
          (dgHomGluingBimodule R (C) (D) (E) (p) (q)) (Y) (Y) := by
  rw [← dgGluingHomTarget_leftAction R (CL) (DR) (V) (pS) (qS) (X) (X)]
  simp only [dgGluingMilnorFreeCoefficientHomIso, Iso.trans_hom, Category.assoc]
  have hc := congrArg (fun f => (pS).map (X).left (X).left ≫ f ≫
    (dgYonedaIso R ((p).obj (Y).left) (representable R ((p).obj (Y).left))).hom)
      (dgGluingMilnorFreeLeftAction_conjugation R d)
  simp only [Category.assoc] at hc
  erw [hc, dgGluingMilnorFreeLeftProjectedHom_evaluate,
    dgGluingMilnorGenerator_leftAction]
  rfl
lemma dgGluingMilnorFreeRightAction_evaluate :
    dgGluingRightAction R (CL) (DR) (M) (X) (X) ≫
        (dgGluingMilnorFreeCoefficientHomIso R d).hom =
      (dgGluingMilnorFreeRightHomIso R d).hom ≫
        dgGluingRightAction R (C) (D)
          (dgHomGluingBimodule R (C) (D) (E) (p) (q)) (Y) (Y) := by
  rw [← dgGluingHomTarget_rightAction R (CL) (DR) (V) (pS) (qS) (X) (X)]
  simp only [dgGluingMilnorFreeCoefficientHomIso, Iso.trans_hom, Category.assoc]
  have hc := congrArg (fun f => (qS).map (X).right (X).right ≫ f ≫
    (dgYonedaIso R ((p).obj (Y).left) (representable R ((p).obj (Y).left))).hom)
      (dgGluingMilnorFreeRightAction_conjugation R d)
  simp only [Category.assoc] at hc
  erw [hc, dgGluingMilnorFreeRightProjectedHom_evaluate,
    dgGluingMilnorGenerator_rightAction]
  rfl
lemma dgGluingMilnorFreeDifference_square :
    dgGluingMilnorActualFreeDifference R d ≫
        (dgGluingMilnorFreeCoefficientHomIso R d).hom =
      (dgGluingMilnorFreePairHomIso R d).hom ≫ dgGluingMilnorRawFreeDifference R d := by
  simp only [dgGluingMilnorActualFreeDifference, dgGluingMilnorRawFreeDifference,
    dgGluingDifference, Preadditive.sub_comp, Preadditive.comp_sub,
    dgGluingMilnorFreePairHomIso, biprod.mapIso_hom, ← Category.assoc,
    biprod.map_fst, biprod.map_snd]
  simp only [Category.assoc, dgGluingMilnorFreeLeftAction_evaluate,
    dgGluingMilnorFreeRightAction_evaluate]
lemma dgGluingMilnorSmallPerfectGeneration : DGGluingMilnorSmallPerfectGeneration R d :=
  dgGluingMilnorSmallPerfectGeneration_of_freeSquare R d
    (dgGluingMilnorFreeDifference_square R d)
end SerrePositivity.InfinityCategories
