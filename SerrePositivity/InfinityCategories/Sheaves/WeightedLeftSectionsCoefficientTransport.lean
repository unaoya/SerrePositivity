module

public import SerrePositivity.InfinityCategories.Sheaves.WeightedSectionsLeftLimitComposition

/-!
概要：元の全切断のleft全空間の値比較を、図式等式に沿って移す計算法則。
方針：元の図式に名前を付け、等式の帰納法で同じ値比較と合成則に戻す。
規約：HTT 5.1.5.6、Kerodon §9.5（Tag 06NC）の既存比較の係数移送。
使われ方：S8 の元の圏に戻す同じ値比較の式を扱う。
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
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C] {E : SSet.{u + 1}} [Quasicategory E]

/-- 元のweightedSections_leftLimitIsoが取る同じ図式の型を固定する。 -/
def weightedLeftSectionsDiagram (O : Presheaf C E) (F : Presheaf C SpaceInfinity.{u}) :
    (SSet.uliftFunctor.{u + 1, u}).obj (smallLeftUnstraightening
      ((SSet.uliftFunctor.{u + 1, u}).map (nerveOppositeIso (C := C)).hom ≫ F)) ⟶ E :=
  (SSet.uliftFunctor.{u + 1, u}).map (smallLeftUnstraighteningProjection
    ((SSet.uliftFunctor.{u + 1, u}).map (nerveOppositeIso (C := C)).hom ≫ F)) ≫
      (SSet.uliftFunctor.{u + 1, u}).map (nerveOppositeIso (C := C)).hom ≫ O

/-- 図式の等式で型だけを移した元の同じ値比較。 -/
def weightedLeftSectionsValueIsoOfDiagramEq (O : Presheaf C E)
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E)
    (F : Presheaf C SpaceInfinity.{u})
    {D : (SSet.uliftFunctor.{u + 1, u}).obj (smallLeftUnstraightening
      ((SSet.uliftFunctor.{u + 1, u}).map (nerveOppositeIso (C := C)).hom ≫ F)) ⟶ E}
    (hD : D = weightedLeftSectionsDiagram O F) (d : JoinCone D) (hd : IsLimitCone d) :
    VertexIso ((weightedSections O hE).app _ (SSet.opObjEquiv.symm (functorVertex F)))
      d.vertex := by
  cases hD
  exact weightedSections_leftLimitIso O hE F d hd

/-- 同じ図式等式による移送は、元の標準極限比較との後合成を保つ。 -/
lemma weightedLeftSectionsValueIsoOfDiagramEq_hom_comp (O : Presheaf C E)
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E)
    (F : Presheaf C SpaceInfinity.{u})
    {D : (SSet.uliftFunctor.{u + 1, u}).obj (smallLeftUnstraightening
      ((SSet.uliftFunctor.{u + 1, u}).map (nerveOppositeIso (C := C)).hom ≫ F)) ⟶ E}
    (hD : D = weightedLeftSectionsDiagram O F) (d e : JoinCone D)
    (hd : IsLimitCone d) (he : IsLimitCone e) :
    (weightedLeftSectionsValueIsoOfDiagramEq O hE F hD d hd).hom ≫
      (limitVertexIso d e hd he).hom =
        (weightedLeftSectionsValueIsoOfDiagramEq O hE F hD e he).hom := by
  cases hD
  exact weightedSections_leftLimitIso_hom_comp O hE F d e hd he

end SerrePositivity.InfinityCategories.Sheaves
