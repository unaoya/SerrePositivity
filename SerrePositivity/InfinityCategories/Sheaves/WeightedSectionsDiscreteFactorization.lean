module

public import SerrePositivity.InfinityCategories.Sheaves.WeightedSectionsOriginalLeftLimitComposition
public import SerrePositivity.InfinityCategories.Sheaves.DiscreteSectionsLeftComparison
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIsoParameterTransport

/-!
概要：元の固定された離散重みの値の同型を、任意の指定left極限との可換三角形で表す。
方針：元の埋め込みの頂点等式の移送を計算し、元の二つの比較の合成則で中間極限を消す。
規約：HTT 5.1.5.6、Kerodon §9.5（Tag 06NC）の既存の固定値比較の計算法則。
使われ方：S8 のweightedSections_discrete_mapで、別の値比較に置き換えず同じ同型を使う。
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
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C] {E : SSet.{u + 1}} [Quasicategory E]

/-- 元の離散値の同型は、同じ頂点移送と任意の指定left極限への同じ比較を可換にする。 -/
lemma weightedSections_discrete_hom_fac (O : Presheaf C E)
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E)
    (P : Cᵒᵖ ⥤ Type u) (hP : HasLimit (sectionsOfDiagram P O))
    (d : JoinCone ((SSet.uliftFunctor.{u + 1, u}).map
      (smallLeftUnstraighteningProjection (discretePresheaf P)) ≫ O)) (hd : IsLimitCone d) :
    let f : (PresheafCat C SpaceInfinity.{u}) _⦋0⦌ → E _⦋0⦌ :=
      fun v => (weightedSections O hE).app _ (SSet.opObjEquiv.symm v)
    (weightedSections_discrete O hE P hP).hom ≫
      (discreteSectionsLeftComparison O P hP d hd).hom =
        eqToHom (congrArg HomotopyCategory.mk
          (congrArg f ((discretePresheafInclusion C).property.1 P))) ≫
            (weightedSections_originalLeftLimitIso O hE (discretePresheaf P) d hd).hom := by
  let f : (PresheafCat C SpaceInfinity.{u}) _⦋0⦌ → E _⦋0⦌ :=
    fun v => (weightedSections O hE).app _ (SSet.opObjEquiv.symm v)
  let hp := (discretePresheafInclusion C).property.1 P
  let D := (SSet.uliftFunctor.{u + 1, u}).map
    (smallLeftUnstraighteningProjection (discretePresheaf P)) ≫ O
  have H : HasLimit D := hE.hasLimit D
  let c := Classical.choose H
  have hc := Classical.choose_spec H
  let w := weightedSections_originalLeftLimitIso O hE (discretePresheaf P) c hc
  let e0 := discreteSectionsLeftComparison O P hP c hc
  have hbody : (weightedSections_discrete O hE P hP).hom =
      eqToHom (congrArg HomotopyCategory.mk (congrArg f hp)) ≫ w.hom ≫ e0.inv := by
    unfold weightedSections_discrete
    change (cast (congrArg (fun v => VertexIso (f v) (sectionsOf P O hP)) hp.symm)
      (w ≪≫ e0.symm)).hom = _
    rw [vertexIso_parameter_source_cast_hom f hp.symm (w ≪≫ e0.symm)]
    rfl
  rw [hbody, ← discreteSectionsLeftComparison_hom_comp O P hP c d hc hd]
  dsimp only [e0, w]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [weightedSections_originalLeftLimitIso_hom_comp]

end SerrePositivity.InfinityCategories.Sheaves
