module

public import SerrePositivity.KST.Spectra.SkeletalStandardLatching
public import SerrePositivity.KST.Spectra.SkeletalWeightedEndTower
public import SerrePositivity.KST.Spectra.WeightedEndReedyKan
public import SerrePositivity.KST.Spectra.PointedWeightedEnd

/-!
概要：通常 Tot の有限骨格の重み付き end は、係数の Reedy 条件の下で Kan。
方針：標準単体の骨格の実際の Reedy cofibrancy を horn 充填の定理へ渡し、点つき end へ移す。
規約：各段の Kan 性を別入力にしない。既存の SkeletalWeightedEnd の対象そのもの。
使われ方：Goerss–Jardine VIII §1。通常 Tot の部分 end の塔の各段。
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits SSet
open SerrePositivity.Reedy
namespace SerrePositivity.KST.Spectra.PointedTotalization
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 部分 Tot の標準単体の骨格の end は、実際の Reedy 条件から Kan となる。 -/
lemma partialEnd_kanComplex (X : CosimplicialObject PointedSimplicialSet.{u})
    (hX : reedyRight simplex modelCategoryQuillen.J.rlp
      (terminal.from (X ⋙ PointedSimplicialSet.forget))) (n : ℕ) :
    KanComplex (PointedWeightedEnd.obj
      (SkeletalWeightedEnd.weight (AsSmall.down ⋙ stdSimplex.{u}) n)
      (AsSmall.down ⋙ X)).right := by
  let : KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections
      (SkeletalWeightedEnd.weight (AsSmall.down ⋙ stdSimplex.{u}) n)
      ((AsSmall.down ⋙ X) ⋙ PointedSimplicialSet.forget)) :=
    WeightedEndReedyKan.kanComplex (stdSimplex.{u} ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.functor (n + 1))
      (X ⋙ PointedSimplicialSet.forget) (SkeletalStandardLatching.reedyCofibrant (n + 1)) hX
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.kanComplex_of_iso (PointedWeightedEnd.underlyingIso
    (SkeletalWeightedEnd.weight (AsSmall.down ⋙ stdSimplex.{u}) n) (AsSmall.down ⋙ X)).symm

end
end SerrePositivity.KST.Spectra.PointedTotalization
