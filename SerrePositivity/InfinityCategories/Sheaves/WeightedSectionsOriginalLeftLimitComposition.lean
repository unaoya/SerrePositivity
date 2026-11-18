module

public import SerrePositivity.InfinityCategories.Sheaves.WeightedSectionsOriginalLeftLimit
public import SerrePositivity.InfinityCategories.Sheaves.WeightedLeftSectionsCoefficientTransport
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.LimitVertexIsoRestriction

/-!
概要：元の圏上のleft全空間への同じ値比較と、指定極限比較の合成則。
方針：元の同じ底同型による制限と係数等式を固定し、頂点射影の制限の法則を使う。
規約：HTT 5.1.5.6、Kerodon §9.5（Tag 06NC）の既存比較の法則。
使われ方：S8 の元の離散重みの固定値比較で、途中の極限の選択を照合する。
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C] {E : SSet.{u + 1}} [Quasicategory E]

/-- 元の圏の同じ値比較に標準極限比較を後合成しても、同じ比較になる。 -/
lemma weightedSections_originalLeftLimitIso_hom_comp (O : Presheaf C E)
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E)
    (F : Presheaf C SpaceInfinity.{u})
    (d e : JoinCone ((SSet.uliftFunctor.{u + 1, u}).map
      (smallLeftUnstraighteningProjection F) ≫ O)) (hd : IsLimitCone d) (he : IsLimitCone e) :
    (weightedSections_originalLeftLimitIso O hE F d hd).hom ≫
      (limitVertexIso d e hd he).hom =
        (weightedSections_originalLeftLimitIso O hE F e he).hom := by
  let b := (SSet.uliftFunctor.{u + 1, u}).mapIso
    (smallLeftUnstraighteningBaseIso (nerveOppositeIso (C := C)) F)
  have hb : IsQCatEquivalence b.hom := (isPrecompositionEquivalence_of_iso b).isQCatEquivalence
  have hD : b.hom ≫ ((SSet.uliftFunctor.{u + 1, u}).map
      (smallLeftUnstraighteningProjection F) ≫ O) = weightedLeftSectionsDiagram O F := by
    dsimp only [weightedLeftSectionsDiagram]
    change (SSet.uliftFunctor.{u + 1, u}).map
      (smallLeftUnstraighteningBaseIso (nerveOppositeIso (C := C)) F).hom ≫ _ = _
    rw [← Category.assoc, ← Functor.map_comp, smallLeftUnstraighteningBaseIso_projection,
      Functor.map_comp, Category.assoc]
  let g (s : JoinCone ((SSet.uliftFunctor.{u + 1, u}).map
      (smallLeftUnstraighteningProjection F) ≫ O)) (hs : IsLimitCone s) :
      VertexIso ((weightedSections O hE).app _ (SSet.opObjEquiv.symm (functorVertex F)))
        (restrictJoinCone s b.hom).vertex :=
    weightedLeftSectionsValueIsoOfDiagramEq O hE F hD (restrictJoinCone s b.hom)
      ((isLimitCone_iff_restrict_equivalentShape b.hom hb s).mp hs)
  have hcompare : ∀ s : JoinCone ((SSet.uliftFunctor.{u + 1, u}).map
      (smallLeftUnstraighteningProjection F) ≫ O), ∀ hs : IsLimitCone s,
    (weightedSections_originalLeftLimitIso O hE F s hs).hom =
      (g s hs).hom ≫ eqToHom (congrArg HomotopyCategory.mk (restrictJoinCone_vertex s b.hom)) := by
    intro s hs
    change ((restrictJoinCone_vertex s b.hom) ▸ (g s hs)).hom = _
    exact vertexIso_transport_target_hom (restrictJoinCone_vertex s b.hom) (g s hs)
  have hdb := (isLimitCone_iff_restrict_equivalentShape b.hom hb d).mp hd
  have heb := (isLimitCone_iff_restrict_equivalentShape b.hom hb e).mp he
  rw [hcompare d hd, hcompare e he, Category.assoc,
    limitVertexIso_restrict_hom b.hom d e hd he hdb heb, ← Category.assoc,
    weightedLeftSectionsValueIsoOfDiagramEq_hom_comp]

end SerrePositivity.InfinityCategories.Sheaves
