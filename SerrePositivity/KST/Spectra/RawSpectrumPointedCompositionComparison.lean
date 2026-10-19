module

public import SerrePositivity.KST.Spectra.RawSpectrumPointedComposition
public import SerrePositivity.KST.Spectra.RawSpectrumMappingComposition

/-!
概要：点つき smash 合成を基礎単体集合へ戻すと、元の全 Hom パラメータの合成になる。
方針：全段の評価と product-to-smash の自然性で照合する。
規約：別の合成へ取り替えない。使われ方：点つき内部 Hom の交換則を元の豊穣 Hom へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping
local instance rawPointedComparisonSimplicialCategory :
    SimplicialCategory PointedSimplicialSet.{u} := PointedEnrichment.simplicialCategory

/-- 元の直積パラメータから smash を経由した合成は、元の BF Hom の合成そのもの。 -/
lemma productToSmash_pointedComposition (X Y : OmegaSpectrum.{u}) (Z : KanSequence.{u}) :
    PointedSimplicialSet.productToSmash (pointedSpace X Y.toKanSequence) (pointedSpace Y Z) ≫
      (pointedComposition X Y Z).right = composition X Y Z := by
  apply hom_ext X Z
  intro n
  rw [Category.assoc, composition_evaluation]
  change PointedSimplicialSet.productToSmash _ _ ≫
      (pointedComposition X Y Z ≫ pointedEvaluation X Z n).right = _
  rw [pointedComposition_evaluation]
  dsimp only [pointedCompositionFamily]
  rw [Under.comp_right, ← Category.assoc,
    ← PointedSimplicialSet.productToSmash_naturality
      (pointedEvaluation X Y.toKanSequence n) (pointedEvaluation Y Z n), Category.assoc]
  rfl

end SerrePositivity.KST.Spectra.RawSpectrumMapping
