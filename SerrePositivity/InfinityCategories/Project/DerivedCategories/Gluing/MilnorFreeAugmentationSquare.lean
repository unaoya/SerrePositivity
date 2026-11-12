module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.MilnorModuleFreeSquare
public import SerrePositivity.KST.SConstruction.DGHomGluingTargetCone
/-!
概要：元自由対角の閉比較射は、固定した両角の代表同型と可換である。
方針：D-19 の同じ実加群正方形を、小模型内の元比較へ戻す。
規約：元の四角形比較と実自由対象を保持する。
使われ方：自由 Hom の比較差の正方形に適用する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded KST.SConstruction
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
private lemma milnorPerfectInputUnderlying {F H : DGFunctor R (A) (E)}
    (hFH : F = H) (B : PerfectDGModule R (A)) :
    (perfectDGExtensionInputIso R (A) (E) hFH B).hom =
      (dgModuleExtensionInputIso R (A) (E) hFH B.val).hom := by
  cases hFH
  rfl
private lemma milnorFreeLeftCornerUnderlying :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorActualFreeLeftCornerIso R d).hom =
    (dgModuleExtension R (C) (E) (p)).onClosed.map
        (dgModuleExtensionRepresentableIso R (A) (C) (L) (dgOdotInputSourcePoint R d)).hom ≫
      (dgModuleExtensionRepresentableIso R (C) (E) (p)
        ((L).obj (dgOdotInputSourcePoint R d))).hom := by
  rfl
private lemma milnorFreeRightCornerUnderlying :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorActualFreeRightCornerIso R d).hom =
    (dgModuleExtension R (D) (E) (q)).onClosed.map
        (dgModuleExtensionRepresentableIso R (A) (D) (G) (dgOdotInputSourcePoint R d)).hom ≫
      (dgModuleExtensionRepresentableIso R (D) (E) (q)
        ((G).obj (dgOdotInputSourcePoint R d))).hom := by
  rfl
private lemma milnorFreeTargetMapUnderlying :
    dgHomGluingTargetMap R (CL) (DR) (V) (pS) (qS) (X) =
    (dgModuleExtensionCompositionAt R (A) (C) (E) (L) (p)
      (representable R (dgOdotInputSourcePoint R d))).hom ≫
      (perfectDGExtensionInputIso R (A) (E) (dgOdotInput_dg_commutes R d) (b).val).hom ≫
    (dgModuleExtensionCompositionAt R (A) (D) (E) (G) (q)
      (representable R (dgOdotInputSourcePoint R d))).inv := by
  have he := dgHomGluingTargetMap_comparisonObject R (CL) (DR) (V) (pS) (qS) (LS) (GS)
    (fun x => (dgSmallPerfectSquareComparisonAt R (A) (C) (D) (E)
      (L) (G) (p) (q) (dgOdotInput_dg_commutes R d) x).hom) (b)
  change dgHomGluingTargetMap R (CL) (DR) (V) (pS) (qS) (X) = _ at he
  refine he.trans ?_
  simp only [dgSmallPerfectSquareComparisonAt, perfectDGExtensionSquareAt,
    perfectDGExtensionSquareViaInputAt, perfectDGExtensionCompositionAt,
    Iso.trans_hom, Iso.symm_hom, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorSourceGenerator,
    dgSmallPerfectBaseRepresentable, dgSmallPerfectEnvelopeRepresentable,
    dgRepresentablePerfectPoint]
  rfl
private lemma milnorFreeTargetMapModule :
    dgHomGluingTargetMap R (CL) (DR) (V) (pS) (qS) (X) =
    (dgModuleExtensionCompositionAt R (A) (C) (E) (L) (p)
      (representable R (dgOdotInputSourcePoint R d))).hom ≫
      (dgModuleExtensionInputIso R (A) (E) (dgOdotInput_dg_commutes R d)
        (representable R (dgOdotInputSourcePoint R d))).hom ≫
    (dgModuleExtensionCompositionAt R (A) (D) (E) (G) (q)
      (representable R (dgOdotInputSourcePoint R d))).inv := by
  have hi := milnorPerfectInputUnderlying R d (dgOdotInput_dg_commutes R d) (b).val
  have he := congrArg (fun f =>
    (dgModuleExtensionCompositionAt R (A) (C) (E) (L) (p)
      (representable R (dgOdotInputSourcePoint R d))).hom ≫ f ≫
    (dgModuleExtensionCompositionAt R (A) (D) (E) (G) (q)
      (representable R (dgOdotInputSourcePoint R d))).inv) hi
  exact (milnorFreeTargetMapUnderlying R d).trans he
lemma dgGluingMilnorActualFreeAugmentation_square :
    dgHomGluingTargetMap R (CL) (DR) (V) (pS) (qS) (X) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorActualFreeRightCornerIso R d).hom =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorActualFreeLeftCornerIso R d).hom := by
  have he := congrArg₂ (fun f g => f ≫ g)
    (milnorFreeTargetMapModule R d) (milnorFreeRightCornerUnderlying R d)
  exact he.trans ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorModuleFreeSquare R d).trans
    (milnorFreeLeftCornerUnderlying R d).symm)
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
