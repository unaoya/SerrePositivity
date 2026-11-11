module

public import SerrePositivity.KST.Spectra.InternalHomExchangeStrength
public import SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeNaturality
public import SerrePositivity.KST.Spectra.RawSpectrumMappingPointed
public import SerrePositivity.KST.Spectra.MappingOmegaSequence

/-!
概要：内部 Hom の源交換は、整合写像空間の二つの構造条件と可換。
方針：源の構造射には交換の自然性、標的の構造射には suspension strength の交換を用いる。
規約：BF 源、任意の Kan 列と点つき cotensor。使われ方：全写像空間での cotensor の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping

/-- cotensor 値への構造射は内部 Hom の交換と可換。 -/
lemma step_exchange (X : OmegaSpectrum.{u}) (Y : KanSequence.{u})
    (A : PointedSimplicialSet.{u}) (n : ℕ) :
    pointedStep X (KanSequence.mapping A Y) n ≫
        (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space) A (Y.level (n + 1)).space).hom =
      (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso (X.level n).space A (Y.level n).space).hom ≫
        (ihom A).map (pointedStep X Y n) := by
  change suspensionHom (X.level n).space ((ihom A).obj (Y.level n).space) ≫
      (ihom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)).map
        (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.map PointedSimplicialSet.circle.{u} A (Y.level n).space ≫
          (ihom A).map (Y.sigma n)) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space) A (Y.level (n + 1)).space).hom =
    (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso (X.level n).space A (Y.level n).space).hom ≫
      (ihom A).map (suspensionHom (X.level n).space (Y.level n).space ≫
        (ihom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)).map (Y.sigma n))
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeTarget.natural_post, InternalHomExchange.suspension_strength_assoc]

/-- 源の構造射による制限も内部 Hom の交換と可換。 -/
lemma restriction_exchange (X : OmegaSpectrum.{u}) (Y : KanSequence.{u})
    (A : PointedSimplicialSet.{u}) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (X.sigma n)
        (PointedObject.basedHom A (Y.level (n + 1)).space) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space) A (Y.level (n + 1)).space).hom =
      (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso (X.level (n + 1)).space A (Y.level (n + 1)).space).hom ≫
        (ihom A).map (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (X.sigma n) (Y.level (n + 1)).space) := by
  simp only [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre]
  exact _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeNaturality.natural_pre_left _ _ _

end SerrePositivity.KST.Spectra.RawSpectrumMapping
