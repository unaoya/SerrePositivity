module

public import SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.QuillenCfReplacementHom
public import SerrePositivity.KST.SConstruction.EnrichedFunctorCollageNerve

/-!
概要：元の豊穣右関手の有向 collage を、両側の cf 対象へ制限した単体的対応圏。
方針：同段・混合・逆向きの全 Hom を個別に計算し、固定 SM7 から局所 Kan 性を得る。
規約：ambient 全体の局所 Kan 性は要求しない。使われ方：HTT 5.2.4.6 の対応圏の nerve。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory HomotopicalAlgebra SSet
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions
noncomputable section
variable {C D : Type v} [Category.{u} C] [Category.{u} D]
  [ModelCategory C] [ModelCategory D] [SimplicialCategory C] [SimplicialCategory D]

/-- 元の collage の下段・上段それぞれで、同じ元の対象が cf であるという条件。 -/
def quillenCfCollageObjects (R : EnrichedFunctor SSet.{u} D C) :
    ObjectProperty (EnrichedFunctorCollageCategory R) := fun X ↦
  match X with
  | .inl X => IsCofibrant X ∧ IsFibrant X
  | .inr Y => IsCofibrant Y ∧ IsFibrant Y

/-- 元の混合 Hom を保持した、cf 対象からなる全充満な単体的対応圏。 -/
abbrev QuillenCfCollage (R : EnrichedFunctor SSet.{u} D C) :=
  (quillenCfCollageObjects R).FullSubcategory

/-- 全充満部分圏の豊穣化は、元の同段・混合 Hom をそのまま保持する。 -/
instance quillenCfCollage_simplicialCategory (R : EnrichedFunctor SSet.{u} D C) :
    SimplicialCategory (QuillenCfCollage R) := inferInstance

variable (R : EnrichedFunctor SSet.{u} D C) {L : C ⥤ D}
  (adj : L ⊣ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor R) [SerrePositivity.Quillen.IsLeftQuillen L]
  (SC : SerrePositivity.Enriched.TensorCotensor SSet.{u} C)
  (SD : SerrePositivity.Enriched.TensorCotensor SSet.{u} D)
  [_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.FixedSimplicialPushoutProduct SC.tensor] [_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.FixedSimplicialPushoutProduct SD.tensor]

include adj SC SD in
/-- cf 部分対応圏の全 Hom は Kan。混合 Hom の fibrancy も元の Quillen 条件から導く。 -/
lemma quillenCfCollage_sHom_kanComplex (X Y : QuillenCfCollage R) :
    KanComplex (SimplicialCategory.sHom X Y) := by
  rcases X with ⟨X, hX⟩
  rcases Y with ⟨Y, hY⟩
  rcases X with X | X <;> rcases Y with Y | Y
  · have : IsCofibrant X := hX.1
    have : IsFibrant Y := hY.2
    exact _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.fixedEnrichedHom_kanComplex SC X Y
  · have : IsCofibrant X := hX.1
    have : IsFibrant Y := hY.2
    exact _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenMixedHom_kanComplex adj SC X Y
  · exact enrichedCollageEmpty_kanComplex
  · have : IsCofibrant X := hX.1
    have : IsFibrant Y := hY.2
    exact _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.fixedEnrichedHom_kanComplex SD X Y

/-- 元の cf 単体的対応圏の coherent nerve。 -/
def QuillenCfCollageInfinity : SSet.{max u v} := SimplicialNerve (QuillenCfCollage R)

include adj SC SD in
/-- cf への制限後の局所 Kan 性から、元の対応圏の nerve は quasicategory。 -/
lemma quillenCfCollageInfinity_quasicategory : Quasicategory (QuillenCfCollageInfinity R) := by
  have : ∀ X Y : QuillenCfCollage R, KanComplex (SimplicialCategory.sHom X Y) :=
    quillenCfCollage_sHom_kanComplex R adj SC SD
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialNerve_quasicategory (QuillenCfCollage R)

end
end SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions
