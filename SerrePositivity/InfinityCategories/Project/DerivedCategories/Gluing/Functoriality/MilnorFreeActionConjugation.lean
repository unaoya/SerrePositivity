module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.CochainModels.Augmentations.MilnorFreeAugmentationSquare
public import SerrePositivity.DifferentialGraded.Functor.DGFunctorHomConjugation
/-!
概要：元自由対角の左右作用は、固定した角の閉同型の共役と整合する。
方針：D-19 で得た閉比較の可換式を前後合成へ移す。
規約：同じ実比較射と全 Hom 共役を保持する。
使われ方：実自由 Hom の比較差の正方形。
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
local notation "a" => dgHomGluingTargetMap R (CL) (DR) (V) (pS) (qS) (X)
local notation "P" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorActualFreeLeftCornerIso R d
local notation "Q" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorActualFreeRightCornerIso R d
lemma dgGluingMilnorActualFreeAugmentation_eq : (a) = (P).hom ≫ (Q).inv := by
  have h := congrArg (fun f => f ≫ (Q).inv)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorActualFreeAugmentation_square R d)
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using h
lemma dgGluingMilnorFreeLeftAction_conjugation :
    eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) ((pS).obj (X).left)) (a) ≫
      (enrichedClosedIsoHomIso (Complex R) (P) (Q)).hom =
    (enrichedClosedIsoHomIso (Complex R) (P) (P)).hom := by
  simp only [enrichedClosedIsoHomIso, enrichedClosedIsoConjugation]
  rw [← Category.assoc, eHom_whisker_exchange, Category.assoc,
    ← eHomWhiskerLeft_comp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorActualFreeAugmentation_square]
lemma dgGluingMilnorFreeRightAction_conjugation :
    eHomWhiskerRight (Complex R) (a)
        (ForgetEnrichment.of (Complex R) ((qS).obj (X).right)) ≫
      (enrichedClosedIsoHomIso (Complex R) (P) (Q)).hom =
    (enrichedClosedIsoHomIso (Complex R) (Q) (Q)).hom := by
  simp only [enrichedClosedIsoHomIso, enrichedClosedIsoConjugation]
  rw [← Category.assoc, ← eHomWhiskerRight_comp,
    dgGluingMilnorActualFreeAugmentation_eq]
  simp only [Iso.inv_hom_id_assoc]
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
