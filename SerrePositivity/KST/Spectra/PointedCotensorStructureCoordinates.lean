module

public import SerrePositivity.KST.Spectra.PointedCotensorCoordinates
public import SerrePositivity.KST.Spectra.RawSpectrumMappingExchange

/-!
概要：自由パラメータ cotensor の構造射を通常の関数複体の構造像へ厳密に照合する。
方針：全 Hom の構造交換則に、自由基点の制限の標的自然性を合成する。
規約：パラメータの Kan 性不要。使われ方：自由区間値の列射の構造区間。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed
namespace SerrePositivity.KST.Spectra.PointedCotensorCoordinates

/-- cotensor 値の構造射への作用は、座標上で元の構造像への後合成となる。 -/
lemma natural_step (K : SSet.{u}) (X : OmegaSpectrum.{u}) (Y : KanSequence.{u}) (n : ℕ) :
    (RawSpectrumMapping.pointedStep X (KanSequence.mapping (PointedObject.adjoin K) Y) n).right ≫
      (iso K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space) (Y.level (n + 1)).space).hom =
    (iso K (X.level n).space (Y.level n).space).hom ≫
      (ihom K).map (RawSpectrumMapping.pointedStep X Y n).right := by
  have hh := congrArg Under.Hom.right
    (RawSpectrumMapping.step_exchange X Y (PointedObject.adjoin K) n)
  simp only [Under.comp_right] at hh
  simp only [iso, Iso.trans_hom, Functor.mapIso_hom, FreePointedHomRestriction.iso]
  rw [← Category.assoc]
  erw [hh]
  rw [Category.assoc]
  erw [FreePointedHomRestriction.natural_post K (RawSpectrumMapping.pointedStep X Y n)]
  exact (Category.assoc _ _ _).symm

end SerrePositivity.KST.Spectra.PointedCotensorCoordinates
