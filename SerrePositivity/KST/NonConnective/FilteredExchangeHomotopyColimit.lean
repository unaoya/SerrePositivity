module
public import SerrePositivity.KST.NonConnective.FilteredExchangeLevelColimit
public import SerrePositivity.KST.NonConnective.SequentialCandidatePiColimitExchange

/-!
概要：実 filtered BF 余錐の整数 π 余極限性を証明し、逐次候補の交換へ代入する。
方針：同じ実置換射影と元の全注入を保つ群比較を使う。
規約：通常 BF 余錐に対する結果。dg 図式の存在・保存や一般 Sp 余極限性は別工程。
使われ方：K-7 e の実 filtered/逐次交換から段別 π 保存の仮定を除去する。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.NonConnective
namespace FilteredExchange
variable {J : Type u} [SmallCategory J] [IsFiltered J]

/-- 同じ外側 filtered BF 比較は元の全注入を保つ。 -/
theorem injection_projection (D : J ⥤ OmegaSpectrum.{u}) (a : J) :
    OmegaSpectrum.filteredSpectrumInjection D a ≫ replacementProjection D =
      levelColimitInjection D a := by
  apply OmegaSpectrum.Hom.ext
  intro k
  exact OmegaSpectrum.filteredSpectrumInjection_comparison D a k

/-- 元の群余極限から置換前の BF 余極限の整数 π への実比較同型。 -/
def levelColimitHomotopyIso (D : J ⥤ OmegaSpectrum.{u}) (j : ℤ) :
    colimit (OmegaSpectrum.spectrumHomotopyGroupDiagram D j) ≅
      GrpCat.of (OmegaSpectrum.homotopyGroup (levelColimitSpectrum D) j) :=
  OmegaSpectrum.filteredSpectrumHomotopyIso D j ≪≫
    ((replacementProjection_piIsomorphism D).groupEquiv j).toGrpIso

/-- 上の同型は同じ実 BF 注入の整数 π 作用を回収する。 -/
theorem levelColimitHomotopyIso_injection (D : J ⥤ OmegaSpectrum.{u}) (j : ℤ) (a : J) :
    colimit.ι (OmegaSpectrum.spectrumHomotopyGroupDiagram D j) a ≫
        (levelColimitHomotopyIso D j).hom =
      GrpCat.ofHom (OmegaSpectrum.homotopyMap (levelColimitInjection D a) j) := by
  rw [levelColimitHomotopyIso, Iso.trans_hom, ← Category.assoc,
    OmegaSpectrum.filteredSpectrumHomotopyIso_ι]
  apply ConcreteCategory.hom_ext
  intro x
  change OmegaSpectrum.homotopyMap (replacementProjection D) j
    (OmegaSpectrum.homotopyMap (OmegaSpectrum.filteredSpectrumInjection D a) j x) = _
  rw [← MonoidHom.comp_apply, ← OmegaSpectrum.homotopyMap_comp, injection_projection]
  rfl

/-- 元の段別 filtered BF 余錐を整数 π へ送った同じ群余錐の普遍性。 -/
def levelHomotopyCoconeIsColimit (D : J ⥤ OmegaSpectrum.{u}) (j : ℤ) :
    IsColimit ((OmegaSpectrum.homotopyFunctor j ⋙ forget₂ CommGrpCat GrpCat).mapCocone
      (levelColimitCocone D)) :=
  IsColimit.ofIsoColimit
    (colimit.isColimit (OmegaSpectrum.spectrumHomotopyGroupDiagram D j))
    (Cocone.ext (levelColimitHomotopyIso D j)
      (fun a => levelColimitHomotopyIso_injection D j a))

/-- 任意の同じ通常 BF filtered 余錐も、整数 π 上で余極限になる。 -/
def homotopy_mapCoconeIsColimit {D : J ⥤ OmegaSpectrum.{u}}
    (c : Cocone D) (hc : IsColimit c) (j : ℤ) :
    IsColimit ((OmegaSpectrum.homotopyFunctor j ⋙ forget₂ CommGrpCat GrpCat).mapCocone c) :=
  IsColimit.ofIsoColimit (levelHomotopyCoconeIsColimit D j)
    ((Cocone.functoriality D
      (OmegaSpectrum.homotopyFunctor j ⋙ forget₂ CommGrpCat GrpCat)).mapIso
      ((levelColimitIsColimit D).uniqueUpToIso hc))

end FilteredExchange

/-- 実 filtered 逐次 BF 余錐の候補 π 余錐。段別 π 保存の追加入力は不要。 -/
def sequentialCandidatePi_mapCoconeIsColimit_of_filtered
    {J : Type u} [SmallCategory J] [IsFiltered J]
    {D : J ⥤ SpectrumSequence.{u}} (c : Cocone D) (hc : IsColimit c) (j : ℤ) :
    IsColimit ((sequentialCandidatePiFunctor j ⋙ forget₂ CommGrpCat GrpCat).mapCocone c) := by
  letI : HasColimitsOfShape J OmegaSpectrum.{u} :=
    ⟨fun E => ⟨_, FilteredExchange.levelColimitIsColimit E⟩⟩
  exact sequentialCandidatePi_mapCoconeIsColimit_of_stages c j (fun a =>
    FilteredExchange.homotopy_mapCoconeIsColimit
      (((evaluation SequentialIndex.{u} OmegaSpectrum.{u}).obj a).mapCocone c)
      (isColimitOfPreserves ((evaluation SequentialIndex.{u} OmegaSpectrum.{u}).obj a) hc) j)

end SerrePositivity.KST.NonConnective
