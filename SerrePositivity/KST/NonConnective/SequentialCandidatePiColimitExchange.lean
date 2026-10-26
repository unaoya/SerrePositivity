module
public import SerrePositivity.KST.NonConnective.SequentialCandidateMapPi
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Whiskering

/-!
概要：実逐次候補の整数 π と外側の余極限の交換を、各段の π 余極限へ帰着する。
方針：元の実注入を保つ群余極限比較を自然同型へ束ね、通常の余極限交換を使う。
規約：dg filtered 図式の作用・段別保存は別入力。群の結果だけで Sp 余極限性は結論しない。
使われ方：K-7 e の filtered 保存に必要な、c4 に依存しない交換部分。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.NonConnective

local instance sequentialGroupColimits : HasColimitsOfShape SequentialIndex.{u} GrpCat.{u} where
  has_colimit F := ⟨_, GrpCat.FilteredColimits.colimitCoconeIsColimit F⟩

/-- 同じ逐次図式の整数 π 図式を全入力で一度に取る。 -/
def sequentialPiDiagramFunctor (j : ℤ) :
    SpectrumSequence.{u} ⥤ (SequentialIndex.{u} ⥤ GrpCat.{u}) where
  obj D := OmegaSpectrum.spectrumHomotopyGroupDiagram D j
  map η := Functor.whiskerRight (Functor.whiskerRight η (OmegaSpectrum.homotopyFunctor j))
    (forget₂ CommGrpCat GrpCat)
  map_id D := by ext a; simp
  map_comp η θ := by ext a; simp

/-- 同じ候補の整数 π 関手を元の群余極限で表示する。 -/
def sequentialCandidatePiColimitIso (j : ℤ) :
    sequentialPiDiagramFunctor.{u} j ⋙ colim ≅
      sequentialCandidatePiFunctor j ⋙ forget₂ CommGrpCat GrpCat :=
  NatIso.ofComponents (fun D => OmegaSpectrum.filteredSpectrumHomotopyIso D j) (by
    intro D E η
    apply colimit.hom_ext
    intro a
    change colimit.ι (OmegaSpectrum.spectrumHomotopyGroupDiagram D j) a ≫
        colimMap ((sequentialPiDiagramFunctor j).map η) ≫
        (OmegaSpectrum.filteredSpectrumHomotopyIso E j).hom = _
    rw [ι_colimMap_assoc]
    dsimp only [sequentialPiDiagramFunctor, Functor.comp_obj]
    rw [OmegaSpectrum.filteredSpectrumHomotopyIso_ι]
    rw [← Category.assoc, OmegaSpectrum.filteredSpectrumHomotopyIso_ι]
    exact congrArg GrpCat.ofHom (sequentialCandidateMap_pi_injection η a j).symm)

/-- 概要：各段の π が指定余錐で余極限なら、同じ実候補の π もその余錐で余極限。
方針：関手圏の点別判定と群余極限関手の余極限保存を使う。
規約：外側添字は任意。filtered 適用時の段別保存や dg 図式の存在は仮定に残す。
使われ方：非連結化の逐次余極限と filtered 余極限の交換の形式部分。 -/
def sequentialCandidatePi_mapCoconeIsColimit_of_stages
    {J : Type u} [SmallCategory J] {D : J ⥤ SpectrumSequence.{u}}
    (c : Cocone D) (j : ℤ)
    (h : ∀ a : SequentialIndex.{u}, IsColimit
      ((((evaluation SequentialIndex.{u} OmegaSpectrum.{u}).obj a ⋙
        OmegaSpectrum.homotopyFunctor j) ⋙ forget₂ CommGrpCat GrpCat).mapCocone c)) :
    IsColimit ((sequentialCandidatePiFunctor j ⋙ forget₂ CommGrpCat GrpCat).mapCocone c) := by
  have hc : IsColimit ((sequentialPiDiagramFunctor j).mapCocone c) :=
    evaluationJointlyReflectsColimits _ h
  have ht : IsColimit ((sequentialPiDiagramFunctor j ⋙ colim).mapCocone c) :=
    isColimitOfPreserves colim hc
  exact IsColimit.mapCoconeEquiv (sequentialCandidatePiColimitIso j) ht

end SerrePositivity.KST.NonConnective
