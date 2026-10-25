module
public import SerrePositivity.InfinityCategories.Derived.Gluing.MilnorFreeActionConjugation
public import SerrePositivity.InfinityCategories.Derived.Gluing.MilnorCornerRepresentableAction
/-!
概要：元自由対象の角への Hom 作用を、固定した両脚の全 Hom 同型で元の代数射へ戻す。
方針：dg 関手の共役自然性と下辺・上辺の代表延長評価を接続する。
規約：元の実対象・同型・Hom 作用を保持する。
使われ方：自由 Hom 比較差の正方形の二成分。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded KST.SConstruction
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
private lemma milnorFreeLeftCorner_evaluate :
    (pS).map (dgGluingMilnorFreeLeft R d) (dgGluingMilnorFreeLeft R d) ≫
      (enrichedClosedIsoHomIso (Complex R) (dgGluingMilnorFreeLeftCornerIso R d)
        (dgGluingMilnorFreeLeftCornerIso R d)).hom ≫ (dgYonedaIso R ((p).obj (Y).left)
        (representable R ((p).obj (Y).left))).hom =
    (dgYonedaIso R (Y).left (representable R (Y).left)).hom ≫
      (p).map (Y).left (Y).left := by
  have h := dgGluingMilnorLowerRepresentable_evaluate R d (Y).left (Y).left
  simp only [dgGluingMilnorLowerRepresentableHomIso,
    dgGluingMilnorFreeLeftCornerIso, enrichedClosedIsoHomIso] at h ⊢
  exact h
lemma dgGluingMilnorFreeLeftProjectedHom_evaluate :
    (pS).map (X).left (X).left ≫
      (enrichedClosedIsoHomIso (Complex R) (dgGluingMilnorActualFreeLeftCornerIso R d)
        (dgGluingMilnorActualFreeLeftCornerIso R d)).hom ≫ (dgYonedaIso R ((p).obj (Y).left)
        (representable R ((p).obj (Y).left))).hom =
    (dgGluingMilnorFreeLeftHomIso R d).hom ≫ (p).map (Y).left (Y).left := by
  have hc := dgFunctorHom_conjugation R (pS) (dgGluingMilnorDiagonalFreeLeftIso R d)
    (dgGluingMilnorDiagonalFreeLeftIso R d)
  have he := congrArg (fun f => f ≫
    (enrichedClosedIsoHomIso (Complex R) (dgGluingMilnorFreeLeftCornerIso R d)
      (dgGluingMilnorFreeLeftCornerIso R d)).hom ≫ (dgYonedaIso R ((p).obj (Y).left)
      (representable R ((p).obj (Y).left))).hom) hc.symm
  have hstep : (pS).map (X).left (X).left ≫
      (enrichedClosedIsoHomIso (Complex R) (dgGluingMilnorActualFreeLeftCornerIso R d)
        (dgGluingMilnorActualFreeLeftCornerIso R d)).hom ≫ (dgYonedaIso R ((p).obj (Y).left)
        (representable R ((p).obj (Y).left))).hom =
    (enrichedClosedIsoHomIso (Complex R) (dgGluingMilnorDiagonalFreeLeftIso R d)
      (dgGluingMilnorDiagonalFreeLeftIso R d)).hom ≫
      (pS).map (dgGluingMilnorFreeLeft R d) (dgGluingMilnorFreeLeft R d) ≫
      (enrichedClosedIsoHomIso (Complex R) (dgGluingMilnorFreeLeftCornerIso R d)
        (dgGluingMilnorFreeLeftCornerIso R d)).hom ≫ (dgYonedaIso R ((p).obj (Y).left)
        (representable R ((p).obj (Y).left))).hom := by
    dsimp only [dgGluingMilnorActualFreeLeftCornerIso, enrichedClosedIsoHomIso]
    rw [← enrichedClosedIsoConjugation_trans (Complex R)
      ((pS).onClosed.mapIso (dgGluingMilnorDiagonalFreeLeftIso R d))
        (dgGluingMilnorFreeLeftCornerIso R d)
      ((pS).onClosed.mapIso (dgGluingMilnorDiagonalFreeLeftIso R d))
        (dgGluingMilnorFreeLeftCornerIso R d)]
    simp only [Category.assoc, enrichedClosedIsoHomIso] at he ⊢
    exact he
  rw [hstep, milnorFreeLeftCorner_evaluate]
  simp only [dgGluingMilnorFreeLeftHomIso, Iso.trans_hom,
    enrichedClosedIsoHomIso, Category.assoc, dgGluingMilnorGenerator]
private lemma milnorFreeRightCorner_evaluate :
    (qS).map (dgGluingMilnorFreeRight R d) (dgGluingMilnorFreeRight R d) ≫
      (enrichedClosedIsoHomIso (Complex R) (dgGluingMilnorFreeRightCornerIso R d)
        (dgGluingMilnorFreeRightCornerIso R d)).hom ≫ (dgYonedaIso R ((p).obj (Y).left)
        (representable R ((p).obj (Y).left))).hom =
    (dgYonedaIso R (Y).right (representable R (Y).right)).hom ≫
      (q).map (Y).right (Y).right := by
  have h := dgGluingMilnorUpperRepresentable_evaluate R d (Y).right (Y).right
  simp only [dgGluingMilnorUpperRepresentableHomIso,
    dgGluingMilnorFreeRightCornerIso, enrichedClosedIsoHomIso] at h ⊢
  exact h
lemma dgGluingMilnorFreeRightProjectedHom_evaluate :
    (qS).map (X).right (X).right ≫
      (enrichedClosedIsoHomIso (Complex R) (dgGluingMilnorActualFreeRightCornerIso R d)
        (dgGluingMilnorActualFreeRightCornerIso R d)).hom ≫ (dgYonedaIso R ((p).obj (Y).left)
        (representable R ((p).obj (Y).left))).hom =
    (dgGluingMilnorFreeRightHomIso R d).hom ≫ (q).map (Y).right (Y).right := by
  have hc := dgFunctorHom_conjugation R (qS) (dgGluingMilnorDiagonalFreeRightIso R d)
    (dgGluingMilnorDiagonalFreeRightIso R d)
  have he := congrArg (fun f => f ≫
    (enrichedClosedIsoHomIso (Complex R) (dgGluingMilnorFreeRightCornerIso R d)
      (dgGluingMilnorFreeRightCornerIso R d)).hom ≫ (dgYonedaIso R ((p).obj (Y).left)
      (representable R ((p).obj (Y).left))).hom) hc.symm
  have hstep : (qS).map (X).right (X).right ≫
      (enrichedClosedIsoHomIso (Complex R) (dgGluingMilnorActualFreeRightCornerIso R d)
        (dgGluingMilnorActualFreeRightCornerIso R d)).hom ≫ (dgYonedaIso R ((p).obj (Y).left)
        (representable R ((p).obj (Y).left))).hom =
    (enrichedClosedIsoHomIso (Complex R) (dgGluingMilnorDiagonalFreeRightIso R d)
      (dgGluingMilnorDiagonalFreeRightIso R d)).hom ≫
      (qS).map (dgGluingMilnorFreeRight R d) (dgGluingMilnorFreeRight R d) ≫
      (enrichedClosedIsoHomIso (Complex R) (dgGluingMilnorFreeRightCornerIso R d)
        (dgGluingMilnorFreeRightCornerIso R d)).hom ≫ (dgYonedaIso R ((p).obj (Y).left)
        (representable R ((p).obj (Y).left))).hom := by
    dsimp only [dgGluingMilnorActualFreeRightCornerIso, enrichedClosedIsoHomIso]
    rw [← enrichedClosedIsoConjugation_trans (Complex R)
      ((qS).onClosed.mapIso (dgGluingMilnorDiagonalFreeRightIso R d))
        (dgGluingMilnorFreeRightCornerIso R d)
      ((qS).onClosed.mapIso (dgGluingMilnorDiagonalFreeRightIso R d))
        (dgGluingMilnorFreeRightCornerIso R d)]
    simp only [Category.assoc, enrichedClosedIsoHomIso] at he ⊢
    exact he
  rw [hstep, milnorFreeRightCorner_evaluate]
  simp only [dgGluingMilnorFreeRightHomIso, Iso.trans_hom,
    enrichedClosedIsoHomIso, Category.assoc, dgGluingMilnorGenerator]
end SerrePositivity.InfinityCategories
