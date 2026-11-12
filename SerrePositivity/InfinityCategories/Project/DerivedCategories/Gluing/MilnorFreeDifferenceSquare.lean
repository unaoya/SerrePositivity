module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.MilnorFreeProjectedHomAction
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomTargetCommaHom
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.MilnorFreeDiagonalComparison
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits DifferentialGraded KST.SConstruction
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "A" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.source
local notation "C" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.left
local notation "D" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.right
local notation "E" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.corner
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
lemma dgGluingMilnorFreeLeftAction_evaluate :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftAction R (CL) (DR) (M) (X) (X) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorFreeCoefficientHomIso R d).hom =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorFreeLeftHomIso R d).hom ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftAction R (C) (D)
          (dgHomGluingBimodule R (C) (D) (E) (p) (q)) (Y) (Y) := by
  rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTarget_leftAction R (CL) (DR) (V) (pS) (qS) (X) (X)]
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorFreeCoefficientHomIso, Iso.trans_hom, Category.assoc]
  have hc := congrArg (fun f => (pS).map (X).left (X).left ≫ f ≫
    (dgYonedaIso R ((p).obj (Y).left) (representable R ((p).obj (Y).left))).hom)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorFreeLeftAction_conjugation R d)
  simp only [Category.assoc] at hc
  erw [hc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorFreeLeftProjectedHom_evaluate,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorGenerator_leftAction]
  rfl
lemma dgGluingMilnorFreeRightAction_evaluate :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightAction R (CL) (DR) (M) (X) (X) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorFreeCoefficientHomIso R d).hom =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorFreeRightHomIso R d).hom ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightAction R (C) (D)
          (dgHomGluingBimodule R (C) (D) (E) (p) (q)) (Y) (Y) := by
  rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTarget_rightAction R (CL) (DR) (V) (pS) (qS) (X) (X)]
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorFreeCoefficientHomIso, Iso.trans_hom, Category.assoc]
  have hc := congrArg (fun f => (qS).map (X).right (X).right ≫ f ≫
    (dgYonedaIso R ((p).obj (Y).left) (representable R ((p).obj (Y).left))).hom)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorFreeRightAction_conjugation R d)
  simp only [Category.assoc] at hc
  erw [hc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorFreeRightProjectedHom_evaluate,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorGenerator_rightAction]
  rfl
lemma dgGluingMilnorFreeDifference_square :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorActualFreeDifference R d ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorFreeCoefficientHomIso R d).hom =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorFreePairHomIso R d).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorRawFreeDifference R d := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorActualFreeDifference, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorRawFreeDifference,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDifference, Preadditive.sub_comp, Preadditive.comp_sub,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorFreePairHomIso, biprod.mapIso_hom, ← Category.assoc,
    biprod.map_fst, biprod.map_snd]
  simp only [Category.assoc, dgGluingMilnorFreeLeftAction_evaluate,
    dgGluingMilnorFreeRightAction_evaluate]
lemma dgGluingMilnorSmallPerfectGeneration : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSmallPerfectGeneration R d :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorSmallPerfectGeneration_of_freeSquare R d
    (dgGluingMilnorFreeDifference_square R d)
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
