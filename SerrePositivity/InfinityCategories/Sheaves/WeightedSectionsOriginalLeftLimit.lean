module

public import SerrePositivity.InfinityCategories.Sheaves.WeightedSectionsLeftLimit
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SmallLeftUnstraighteningBaseIso

/-!
概要：元の全重み切断の値を、元の前層形状の小さい left 全空間の指定極限へ接続する。
方針：反対 nerve の底同型に沿う既存の全空間の同型で指定極限錐を制限する。
  文献対応：HTT 5.1.5.6、Kerodon Remark 5.6.2.18（Tag 0271）、S8 の離散重みの比較。
規約：元の前層と係数の形状を保持し、指定した同じ極限錐の頂点を返す。
-/

@[expose] public noncomputable section
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

/-- 元の重みと係数の形状の小さい left 全空間で、同じ指定極限の頂点と比較する。
HTT 5.1.5.6、Kerodon Remark 5.6.2.18（Tag 0271）、底同型に沿う係数移送の合成則。 -/
def weightedSections_originalLeftLimitIso (O : Presheaf C E)
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E)
    (F : Presheaf C SpaceInfinity.{u})
    (d : JoinCone ((SSet.uliftFunctor.{u + 1, u}).map (smallLeftUnstraighteningProjection F) ≫ O))
    (hd : IsLimitCone d) :
    VertexIso ((weightedSections O hE).app _ (SSet.opObjEquiv.symm (functorVertex F))) d.vertex := by
  let b := (SSet.uliftFunctor.{u + 1, u}).mapIso
    (smallLeftUnstraighteningBaseIso (nerveOppositeIso (C := C)) F)
  let t := restrictJoinCone d b.hom
  have ht := (isLimitCone_iff_restrict_equivalentShape b.hom
    (isPrecompositionEquivalence_of_iso b).isQCatEquivalence d).mp hd
  have he : b.hom ≫ ((SSet.uliftFunctor.{u + 1, u}).map
      (smallLeftUnstraighteningProjection F) ≫ O) =
      (SSet.uliftFunctor.{u + 1, u}).map (smallLeftUnstraighteningProjection
        ((SSet.uliftFunctor.{u + 1, u}).map (nerveOppositeIso (C := C)).hom ≫ F)) ≫
          (SSet.uliftFunctor.{u + 1, u}).map (nerveOppositeIso (C := C)).hom ≫ O := by
    change (SSet.uliftFunctor.{u + 1, u}).map
      (smallLeftUnstraighteningBaseIso (nerveOppositeIso (C := C)) F).hom ≫ _ = _
    rw [← Category.assoc, ← Functor.map_comp, smallLeftUnstraighteningBaseIso_projection,
      Functor.map_comp, Category.assoc]
  have htransport : ∀ D, D =
      (SSet.uliftFunctor.{u + 1, u}).map (smallLeftUnstraighteningProjection
        ((SSet.uliftFunctor.{u + 1, u}).map (nerveOppositeIso (C := C)).hom ≫ F)) ≫
          (SSet.uliftFunctor.{u + 1, u}).map (nerveOppositeIso (C := C)).hom ≫ O →
      ∀ s : JoinCone D, IsLimitCone s →
        VertexIso ((weightedSections O hE).app _ (SSet.opObjEquiv.symm (functorVertex F))) s.vertex := by
    intro D h s hs
    cases h
    exact weightedSections_leftLimitIso O hE F s hs
  have e := htransport _ he t ht
  exact (restrictJoinCone_vertex d b.hom) ▸ e

end SerrePositivity.InfinityCategories.Sheaves
