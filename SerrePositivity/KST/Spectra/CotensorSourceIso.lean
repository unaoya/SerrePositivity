module

public import SerrePositivity.KST.Spectra.CotensorRestriction
public import SerrePositivity.KST.Spectra.SpectrumWhiteheadEquivalence

/-!
概要：源の厳密な同型による BF cotensor の比較辺は実際の Sp の同値。
方針：BF 置換射影と、置換前の内部 Hom の制限同型で各段の π 同型を打ち消す。
規約：cotensor の厳密な関手性は入力しない。使われ方：円の商表示から通常の円への比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum

/-- 源の同型による BF cotensor の制限は各段で全基点 π 同型。 -/
lemma cotensorPre_levelwise_of_isIso {A B : PointedSimplicialSet.{u}} (i : A ⟶ B) [IsIso i]
    (Y : OmegaSpectrum.{u}) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism ((cotensorPre i Y).app n).right := by
  apply _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism.of_comp (g := ((cotensorProjection A Y).app n).right) _
    (cotensorProjection_piIsomorphism A Y n)
  have h := congrArg Under.Hom.right (cotensorPre_comparison i Y n)
  simp only [Under.comp_right] at h
  rw [h]
  have hi : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i (Y.level n).space).right := by
    let e := (internalHom.flip.obj (Y.level n).space).mapIso (asIso i).op
    have he : _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i (Y.level n).space = e.hom := by
      rw [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre]
      rfl
    rw [he]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanPiIsomorphism.of_iso
      (X := (PointedObject.basedHom B (Y.level n).space).right)
      (Y := (PointedObject.basedHom A (Y.level n).space).right)
      (PointedSimplicialSet.forget.mapIso e)
  exact (cotensorProjection_piIsomorphism B Y n).comp hi

local instance sourceIsoSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
local instance sourceIsoHomKan (X Y : OmegaSpectrum.{u}) :
    KanComplex (SimplicialCategory.sHom X Y) := OmegaSpectrum.mappingSpace_kanComplex X Y

/-- 元の源の同型が与える BF cotensor の指定された比較辺は Sp の同値。 -/
lemma cotensorPre_isInvertible_of_isIso {A B : PointedSimplicialSet.{u}}
    (i : A ⟶ B) [IsIso i] (Y : OmegaSpectrum.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (cotensorPre i Y)) :=
  SpectrumMappingAcyclic.isInvertible_of_levelwise _ (cotensorPre_levelwise_of_isIso i Y)

end SerrePositivity.KST.Spectra.OmegaSpectrum
