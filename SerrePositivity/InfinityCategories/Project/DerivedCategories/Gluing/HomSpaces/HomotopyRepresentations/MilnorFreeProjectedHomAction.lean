module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Functoriality.MilnorFreeActionConjugation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Functoriality.MilnorCornerRepresentableAction
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded KST.SConstruction
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "A" => _root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R d.source
local notation "C" => _root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R d.left
local notation "D" => _root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R d.right
local notation "E" => _root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R d.corner
local notation "L" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.top
local notation "G" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.side
local notation "p" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.lower
local notation "q" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.upper
local notation "CL" => DGSmallPerfectArrowTarget R (A) (C) (L)
local notation "DR" => DGSmallPerfectArrowTarget R (A) (D) (G)
local notation "V" => DGSmallPerfectSquareCorner R (A) (C) (D) (E) (L) (G) (p) (q)
local notation "pS" => dgSmallPerfectSquareLeftMap R (A) (C) (D) (E) (L) (G) (p) (q)
local notation "qS" => dgSmallPerfectSquareRightMap R (A) (C) (D) (E) (L) (G) (p) (q)
local notation "M" => dgHomGluingBimodule R (CL) (DR) (V) (pS) (qS)
local notation "LS" => dgSmallPerfectArrow R (A) (C) (L)
local notation "GS" => dgSmallPerfectArrow R (A) (D) (G)
local notation "b" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorSourceGenerator R d
local notation "X" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorActualFreeObject R d
local notation "Y" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorGenerator R d
private lemma milnorFreeLeftCorner_evaluate :
    (pS).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorFreeLeft R d) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorFreeLeft R d) ≫
      (enrichedClosedIsoHomIso (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorFreeLeftCornerIso R d)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorFreeLeftCornerIso R d)).hom ≫ (dgYonedaIso R ((p).obj (Y).left)
        (representable R ((p).obj (Y).left))).hom =
    (dgYonedaIso R (Y).left (representable R (Y).left)).hom ≫
      (p).map (Y).left (Y).left := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorLowerRepresentable_evaluate R d (Y).left (Y).left
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorLowerRepresentableHomIso,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorFreeLeftCornerIso, enrichedClosedIsoHomIso] at h ⊢
  exact h
lemma dgGluingMilnorFreeLeftProjectedHom_evaluate :
    (pS).map (X).left (X).left ≫
      (enrichedClosedIsoHomIso (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorActualFreeLeftCornerIso R d)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorActualFreeLeftCornerIso R d)).hom ≫ (dgYonedaIso R ((p).obj (Y).left)
        (representable R ((p).obj (Y).left))).hom =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorFreeLeftHomIso R d).hom ≫ (p).map (Y).left (Y).left := by
  have hc := dgFunctorHom_conjugation R (pS) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorDiagonalFreeLeftIso R d)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorDiagonalFreeLeftIso R d)
  have he := congrArg (fun f => f ≫
    (enrichedClosedIsoHomIso (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorFreeLeftCornerIso R d)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorFreeLeftCornerIso R d)).hom ≫ (dgYonedaIso R ((p).obj (Y).left)
      (representable R ((p).obj (Y).left))).hom) hc.symm
  have hstep : (pS).map (X).left (X).left ≫
      (enrichedClosedIsoHomIso (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorActualFreeLeftCornerIso R d)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorActualFreeLeftCornerIso R d)).hom ≫ (dgYonedaIso R ((p).obj (Y).left)
        (representable R ((p).obj (Y).left))).hom =
    (enrichedClosedIsoHomIso (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorDiagonalFreeLeftIso R d)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorDiagonalFreeLeftIso R d)).hom ≫
      (pS).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorFreeLeft R d) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorFreeLeft R d) ≫
      (enrichedClosedIsoHomIso (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorFreeLeftCornerIso R d)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorFreeLeftCornerIso R d)).hom ≫ (dgYonedaIso R ((p).obj (Y).left)
        (representable R ((p).obj (Y).left))).hom := by
    dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorActualFreeLeftCornerIso, enrichedClosedIsoHomIso]
    rw [← enrichedClosedIsoConjugation_trans (Complex R)
      ((pS).onClosed.mapIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorDiagonalFreeLeftIso R d))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorFreeLeftCornerIso R d)
      ((pS).onClosed.mapIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorDiagonalFreeLeftIso R d))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorFreeLeftCornerIso R d)]
    simp only [Category.assoc, enrichedClosedIsoHomIso] at he ⊢
    exact he
  rw [hstep, milnorFreeLeftCorner_evaluate]
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorFreeLeftHomIso, Iso.trans_hom,
    enrichedClosedIsoHomIso, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorGenerator]
private lemma milnorFreeRightCorner_evaluate :
    (qS).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorFreeRight R d) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorFreeRight R d) ≫
      (enrichedClosedIsoHomIso (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorFreeRightCornerIso R d)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorFreeRightCornerIso R d)).hom ≫ (dgYonedaIso R ((p).obj (Y).left)
        (representable R ((p).obj (Y).left))).hom =
    (dgYonedaIso R (Y).right (representable R (Y).right)).hom ≫
      (q).map (Y).right (Y).right := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorUpperRepresentable_evaluate R d (Y).right (Y).right
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorUpperRepresentableHomIso,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorFreeRightCornerIso, enrichedClosedIsoHomIso] at h ⊢
  exact h
lemma dgGluingMilnorFreeRightProjectedHom_evaluate :
    (qS).map (X).right (X).right ≫
      (enrichedClosedIsoHomIso (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorActualFreeRightCornerIso R d)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorActualFreeRightCornerIso R d)).hom ≫ (dgYonedaIso R ((p).obj (Y).left)
        (representable R ((p).obj (Y).left))).hom =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorFreeRightHomIso R d).hom ≫ (q).map (Y).right (Y).right := by
  have hc := dgFunctorHom_conjugation R (qS) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorDiagonalFreeRightIso R d)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorDiagonalFreeRightIso R d)
  have he := congrArg (fun f => f ≫
    (enrichedClosedIsoHomIso (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorFreeRightCornerIso R d)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorFreeRightCornerIso R d)).hom ≫ (dgYonedaIso R ((p).obj (Y).left)
      (representable R ((p).obj (Y).left))).hom) hc.symm
  have hstep : (qS).map (X).right (X).right ≫
      (enrichedClosedIsoHomIso (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorActualFreeRightCornerIso R d)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorActualFreeRightCornerIso R d)).hom ≫ (dgYonedaIso R ((p).obj (Y).left)
        (representable R ((p).obj (Y).left))).hom =
    (enrichedClosedIsoHomIso (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorDiagonalFreeRightIso R d)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorDiagonalFreeRightIso R d)).hom ≫
      (qS).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorFreeRight R d) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorFreeRight R d) ≫
      (enrichedClosedIsoHomIso (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorFreeRightCornerIso R d)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorFreeRightCornerIso R d)).hom ≫ (dgYonedaIso R ((p).obj (Y).left)
        (representable R ((p).obj (Y).left))).hom := by
    dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorActualFreeRightCornerIso, enrichedClosedIsoHomIso]
    rw [← enrichedClosedIsoConjugation_trans (Complex R)
      ((qS).onClosed.mapIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorDiagonalFreeRightIso R d))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorFreeRightCornerIso R d)
      ((qS).onClosed.mapIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorDiagonalFreeRightIso R d))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorFreeRightCornerIso R d)]
    simp only [Category.assoc, enrichedClosedIsoHomIso] at he ⊢
    exact he
  rw [hstep, milnorFreeRightCorner_evaluate]
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorFreeRightHomIso, Iso.trans_hom,
    enrichedClosedIsoHomIso, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorGenerator]
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
