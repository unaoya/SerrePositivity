module

public import SerrePositivity.InfinityCategories.Sheaves.WeightedSectionsLeftLimit
public import SerrePositivity.InfinityCategories.Sheaves.NativeLeftSectionsCoefficientTransport

/-!
概要：元の全切断のleft全空間への固定値比較と、指定極限の頂点比較の合成則。
方針：元の式の定数部分を固定し、同じ係数等式による移送の合成則を使う。
規約：HTT 5.1.5.6、Kerodon §9.5（Tag 06NC）の既存比較の法則。新しい値比較を選ばない。
使われ方：S8 の元の離散重みの固定値比較の照合。
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
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C] {E : SSet.{u + 1}} [Quasicategory E]

/-- 元の同じ全切断の値の比較は、指定極限の比較との後合成を保つ。 -/
lemma weightedSections_leftLimitIso_hom_comp (O : Presheaf C E)
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E)
    (F : Presheaf C SpaceInfinity.{u})
    (d e : JoinCone ((SSet.uliftFunctor.{u + 1, u}).map (smallLeftUnstraighteningProjection
      ((SSet.uliftFunctor.{u + 1, u}).map (nerveOppositeIso (C := C)).hom ≫ F)) ≫
        (SSet.uliftFunctor.{u + 1, u}).map (nerveOppositeIso (C := C)).hom ≫ O))
    (hd : IsLimitCone d) (he : IsLimitCone e) :
    (weightedSections_leftLimitIso O hE F d hd).hom ≫ (limitVertexIso d e hd he).hom =
      (weightedSections_leftLimitIso O hE F e he).hom := by
  let P := (SSet.uliftFunctor.{u + 1, u}).map (nerveOppositeIso (C := C)).hom ≫ F
  let O' := (fixedYonedaDomainIso C).inv ≫ O
  let v := SSet.opObjEquiv.symm (functorVertex P)
  let c := (nativeWeightedSections_valueTransport O' hE v).cone
  have hc := nativeWeightedSections_valueTransport_isLimit O' hE v
  have hv := nativeWeightedSections_valueTransport_vertex O' hE v
  let ew : VertexIso ((weightedSections O hE).app _
      (SSet.opObjEquiv.symm (functorVertex F))) c.vertex :=
    weightedSections_nativeLimitIso O hE (SSet.opObjEquiv.symm (functorVertex F)) c hc
  let ew' : VertexIso ((weightedSections O hE).app _
      (SSet.opObjEquiv.symm (functorVertex F))) (nativeLeftSectionsValue P O' hE) := by
    change VertexIso _ ((nativeWeightedSections O' hE).app _ v)
    exact hv ▸ ew
  have hD : (SSet.uliftFunctor.{u + 1, u}).map (smallLeftUnstraighteningProjection P) ≫
      (SSet.uliftFunctor.{u + 1, u}).map (nerveOppositeIso (C := C)).hom ≫ O =
        nativeLeftSectionsDiagram P O' := by
    dsimp only [nativeLeftSectionsDiagram, O', fixedYonedaDomainIso, Iso.trans_inv,
      Functor.mapIso_inv, Iso.symm_inv]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
  have hcompare : ∀ t : JoinCone
      ((SSet.uliftFunctor.{u + 1, u}).map (smallLeftUnstraighteningProjection P) ≫
        (SSet.uliftFunctor.{u + 1, u}).map (nerveOppositeIso (C := C)).hom ≫ O),
      ∀ ht : IsLimitCone t,
      (weightedSections_leftLimitIso O hE F t ht).hom = ew'.hom ≫
        (nativeLeftSectionsValueIsoOfDiagramEq P O' hE hD t ht).hom := by
    intro t ht
    rfl
  rw [hcompare d hd, hcompare e he, Category.assoc,
    nativeLeftSectionsValueIsoOfDiagramEq_hom_comp]

end SerrePositivity.InfinityCategories.Sheaves
