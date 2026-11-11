module

public import SerrePositivity.KST.Spectra.PointedSmallProduct
public import SerrePositivity.KST.Spectra.KanSequenceAdjointMap
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
概要：任意の小さい Kan 列の族の段ごとの積と Ω 条件。
方針：loop の小積保存を使い、随伴構造を全座標の随伴の積として定義する。
規約：空の族も含む。単射構造射の検証は別モジュール。
使われ方：BF 1978 §2、HA §1.4.2。Sp の小積の具体的な対象。
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalClosed SSet
namespace SerrePositivity.KST.Spectra.SmallProductKanSequence
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {S : Type u}

/-- loop で写した小積の fan の実際の極限性。 -/
def loopFanIsLimit (X : S → PointedSimplicialSet.{u}) :
    IsLimit (Fan.mk (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (PointedSmallProduct.obj X))
      (fun s ↦ PointedObject.basedHomMap PointedSimplicialSet.circle.{u}
        (PointedSmallProduct.projection X s))) :=
  isLimitFanMkObjOfIsLimit (ihom PointedSimplicialSet.circle.{u}) X
    (PointedSmallProduct.projection X) (PointedSmallProduct.isLimit X)

/-- loop と任意の具体的小積の交換同型。 -/
def loopIso (X : S → PointedSimplicialSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (PointedSmallProduct.obj X) ≅
      PointedSmallProduct.obj (fun s ↦ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (X s)) :=
  (loopFanIsLimit X).conePointUniqueUpToIso (PointedSmallProduct.isLimit _)

@[reassoc (attr := simp)]
lemma loopIso_projection (X : S → PointedSimplicialSet.{u}) (s : S) :
    (loopIso X).hom ≫ PointedSmallProduct.projection _ s =
      PointedObject.basedHomMap PointedSimplicialSet.circle.{u}
        (PointedSmallProduct.projection X s) :=
  (loopFanIsLimit X).conePointUniqueUpToIso_hom_comp
    (PointedSmallProduct.isLimit _) (Discrete.mk s)

/-- 族の随伴構造を、小積の loop への射へまとめる。 -/
def adjoint (X : S → KanSequence.{u}) (n : ℕ) :
    PointedSmallProduct.obj (fun s ↦ ((X s).level n).space) ⟶
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (PointedSmallProduct.obj (fun s ↦ ((X s).level (n + 1)).space)) :=
  PointedSmallProduct.map (fun s ↦ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv ((X s).level n).space
    ((X s).level (n + 1)).space ((X s).sigma n)) ≫ (loopIso _).inv

/-- 任意の小さい Kan 列の族の具体的な積の列。 -/
def obj (X : S → KanSequence.{u}) : KanSequence.{u} where
  level n := ⟨PointedSmallProduct.obj (fun s ↦ ((X s).level n).space), inferInstance⟩
  sigma n := uncurry (adjoint X n)

/-- 構成した列の随伴構造は小積の随伴射そのもの。 -/
lemma obj_adjoint (X : S → KanSequence.{u}) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv ((obj X).level n).space ((obj X).level (n + 1)).space
      ((obj X).sigma n) = adjoint X n := curry_uncurry _

/-- 元の各列の Ω 条件は任意の小積で保たれる。 -/
lemma omegaCondition (X : S → KanSequence.{u}) (hX : ∀ s, (X s).OmegaCondition) :
    (obj X).OmegaCondition := by
  intro n
  rw [obj_adjoint]
  let e := loopIso (fun s ↦ ((X s).level (n + 1)).space)
  have he : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism e.inv.right :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanPiIsomorphism.of_iso
      (X := (PointedSmallProduct.obj (fun s ↦ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace ((X s).level (n + 1)).space)).right)
      (Y := (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (PointedSmallProduct.obj
        (fun s ↦ ((X s).level (n + 1)).space))).right)
      (PointedSimplicialSet.forget.mapIso e.symm)
  exact (PointedSmallProduct.map_piIsomorphism _ (fun s ↦ hX s n)).comp
    he

end
end SerrePositivity.KST.Spectra.SmallProductKanSequence
