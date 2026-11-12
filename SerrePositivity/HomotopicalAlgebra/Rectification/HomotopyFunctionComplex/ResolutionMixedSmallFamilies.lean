module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ResolutionMixedCoherentTriangles
public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.NerveSmallFamilies
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.UniverseLiftProductParameter

/-!
# 中断した任意モデル源への一般化：ResolutionMixedSmallFamilies

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Entire mixed triangle families in the original Hom universe on every external chain。

## 方針（定義・証明）
整合図式の値変更による厳密化と宇宙縮小の問題に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0326][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0326
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Entire mixed triangle families in the original Hom universe on every external chain
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.SimplicialModel SerrePositivity.HomotopyFunctionComplex
open ResolutionMixedDiagram NerveBiparameterMaps

namespace SerrePositivity.HomotopyFunctionComplex.ResolutionMixedSmallFamilies
variable (C : Type u) [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

abbrev tuples := cornerA C ⋙ ResolutionArrowTuples.tuples C
abbrev smallParameter := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.product (tuples C)
  (SSet.stdSimplex.{v}.obj (SimplexCategory.mk 2))
abbrev parameterIso : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted.{u} (smallParameter C) ≅
    ResolutionMixedBoundary.fullParameter C := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.iso (tuples C) 2

/-- Change coordinates on the same whole coherent triangle system. -/
def system (side : Bool) : NerveMovingParameter.System.{u, v}
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted.{u} (smallParameter C)) (smallValues C) :=
  restrict _ _ _ (parameterIso C).hom (ResolutionMixedCoherentTriangles.coherent C hcof hfib side)

/-- Every external chain carries an entire small tuple-and-triangle family. -/
def family (side : Bool) {n : ℕ} (c : ComposableArrows (Index C) n) :
    (smallParameter C).obj (c.obj 0) ⊗ SSet.stdSimplex.{v}.obj (SimplexCategory.mk n) ⟶
      (smallValues C).obj (c.obj (Fin.last n)) :=
  NerveSmallFamilies.family (smallParameter C) (smallValues C) (system C hcof hfib side) c

lemma family_naturality (side : Bool) {n m : ℕ} (c : ComposableArrows (Index C) n)
    (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :
    (smallParameter C).obj (c.obj 0) ◁ SSet.stdSimplex.map θ ≫ family C hcof hfib side c =
      (((smallParameter C).map (c.map (homOfLE (Fin.zero_le (θ.toOrderHom 0))))) ▷
        SSet.stdSimplex.obj (SimplexCategory.mk m) ≫
        family C hcof hfib side ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)) ≫
      (smallValues C).map (c.map (homOfLE (Fin.le_last (θ.toOrderHom (Fin.last m))))) :=
  NerveSmallFamilies.family_naturality _ _ _ c θ

lemma point_recover (side : Bool) (p : Index C) :
    NerveSmallFamilies.point (smallParameter C) (smallValues C) (system C hcof hfib side) p =
    RelativeChoiceSpace.family (ResolutionMixedTriangles.oldInclusion C p)
      (ResolutionMixedTriangles.oldBoundary C p)
      (ResolutionMixedTriangles.oldTriangle C hcof hfib p side) := by
  apply (congrArg _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.lower
    ((evaluate_restrict (ResolutionMixedBoundary.fullParameter C) (smallValues C)
      (ResolutionMixedCoherentTriangles.coherent C hcof hfib side)
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted.{u} (smallParameter C)) (parameterIso C).hom p).trans
      (congrArg (fun k => (parameterIso C).hom.app p ≫ k)
        (ResolutionMixedCoherentTriangles.coherent_evaluate C hcof hfib side p)))).trans
  change _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.lower ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.iso (tuples C) 2).hom.app p ≫
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexTensorMap _) = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.hom_family, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.lower_map]
  rfl

abbrev smallIntervalParameter := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.product (tuples C)
  (SSet.stdSimplex.{v}.obj (SimplexCategory.mk 1))
abbrev smallFaceMap (k : Fin 3) : smallIntervalParameter C ⟶ smallParameter C :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertical (SSet.stdSimplex.δ k) (tuples C)
abbrev intervalParameterIso : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted.{u} (smallIntervalParameter C) ≅
    ResolutionMixedIntervalRestrictions.intervalParameters C :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.iso (tuples C) 1

def faceSystem (side : Bool) (k : Fin 3) : NerveMovingParameter.System.{u, v}
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted.{u} (smallIntervalParameter C)) (smallValues C) :=
  restrict _ _ _ (intervalParameterIso C).hom (ResolutionMixedFaceSystems.faces C hcof hfib side k)

lemma system_face (side : Bool) (k : Fin 3) : system C hcof hfib side ≫ restriction _ _
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DiagramUniverseLift.NerveMovingParameter.lifted (smallValues C))
    (Functor.whiskerRight (smallFaceMap C k) SSet.uliftFunctor.{u, v}) =
    faceSystem C hcof hfib side k := by
  have hc : Functor.whiskerRight (smallFaceMap C k) SSet.uliftFunctor.{u, v} ≫
      (parameterIso C).hom = (intervalParameterIso C).hom ≫
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertical (SSet.stdSimplex.δ k) (parameters C) :=
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.operator (tuples C) (SimplexCategory.δ k)
  change (ResolutionMixedCoherentTriangles.coherent C hcof hfib side ≫
    restriction _ _ _ (parameterIso C).hom) ≫ _ = _
  rw [Category.assoc, restriction_comp, hc, ← restriction_comp, ← Category.assoc,
    ResolutionMixedCoherentTriangles.coherent_face]
  rfl

abbrev faceFamily (side : Bool) (k : Fin 3) {n : ℕ} (c : ComposableArrows (Index C) n) :=
  NerveSmallFamilies.family (smallIntervalParameter C) (smallValues C)
    (faceSystem C hcof hfib side k) c

lemma family_face (side : Bool) (k : Fin 3) {n : ℕ} (c : ComposableArrows (Index C) n) :
    faceFamily C hcof hfib side k c =
    ((smallFaceMap C k).app (c.obj 0) ▷ SSet.stdSimplex.obj (SimplexCategory.mk n)) ≫
      family C hcof hfib side c :=
  (congrArg (fun a => NerveSmallFamilies.family (smallIntervalParameter C) (smallValues C) a c)
    (system_face C hcof hfib side k).symm).trans
    (NerveSmallFamilies.family_restrict _ _ _ _ _ c)

lemma shared_diagonal {n : ℕ} (c : ComposableArrows (Index C) n) :
    faceFamily C hcof hfib true 1 c = faceFamily C hcof hfib false 1 c := by
  apply congrArg (fun a => NerveSmallFamilies.family (smallIntervalParameter C) (smallValues C) a c)
  exact congrArg (restrict _ _ _ (intervalParameterIso C).hom)
    (ResolutionMixedFaceSystems.shared_diagonal C hcof hfib)

end SerrePositivity.HomotopyFunctionComplex.ResolutionMixedSmallFamilies
