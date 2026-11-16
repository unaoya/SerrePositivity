module

public import SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.SieveTensorSectionsNaturality

/-!
概要：任意の集合重みの元の射に対して、テンソルと指定切断の比較を全族で結ぶ。
方針：既存G8の随伴・切断比較・指定極限比較の三つの一般の自然性を合成する。
規約：HTT §5.1.5、Kerodon §9.5（Tag 06NC）の既存比較の自然性。係数の層条件は不要。
使われ方：S8 の一般の集合重みの射の比較で、篩包含に限定しない既存法則を再利用する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Project.SetWeightedTensors
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
namespace SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories

/-- 元の一般の集合重みの射のテンソルの前合成と、元の指定切断辺の後合成の自然性。 -/
def setWeightTensorSections_shapeIso {I : Type u} [SmallCategory I]
    {P Q : I ⥤ Type u} (φ : P ⟶ Q)
    {E : SSet.{u + 1}} [Quasicategory E] (hE : IsPresentable E) (M : E _⦋0⦌)
    (F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve I) ⟶ E)
    (cP : JoinCone (SetWeight.diagram P F)) (hcP : IsLimitCone cP)
    (cQ : JoinCone (SetWeight.diagram Q F)) (hcQ : IsLimitCone cQ) :
    FunctorIso
      (precompose (functorVertex F)
        (Truncated.HomotopyCategory.homMk (SetWeight.tensorWeightEdge hE M φ).toTruncated) ≫
          (SetWeight.tensorSpaceFunctor_setWeightHomNatural P hE M F cP hcP).hom)
      ((SetWeight.tensorSpaceFunctor_setWeightHomNatural Q hE M F cQ hcQ).hom ≫
        postcompose M (Truncated.HomotopyCategory.homMk
          (SetWeight.sectionsMap φ F cP hcP cQ hcQ).toTruncated)) := by
  let G := F ≫ (spaceTensorData hE M).hom
  have h0 := (SetWeight.tensorSpaceFunctor_diagramHom_weight_naturality hE M φ F).postcomp
    ((SetWeight.sectionsEquivalenceNatural P G).hom ≫
      (setWeightSectionsLimitTail P hE M F cP hcP).hom)
  have h1 := ((setWeightSectionsEquivalenceNatural_shapeIso φ G).postcomp
    (setWeightSectionsLimitTail P hE M F cP hcP).hom).precomp
    (tensorSpaceFunctor_diagramHom hE M (spaceDiagram Q) F).hom
  have h2 := (setWeightSectionsLimitTail_shapeIso φ hE M F cP hcP cQ hcQ).precomp
    ((tensorSpaceFunctor_diagramHom hE M (spaceDiagram Q) F).hom ≫
      (SetWeight.sectionsEquivalenceNatural Q G).hom)
  simp only [Category.assoc] at h0 h1 h2
  simpa only [tensorSpaceFunctor_setWeightHomNatural_hom_factor, G,
    SSet.Edge.toTruncated, FunctorIso, Category.assoc] using (h0 ≪≫ h1) ≪≫ h2

end SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories
