module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CatInfinity.StrictCoherentNatTransComponent
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.DiagramComparisons.HomotopyPrism
public import SerrePositivity.InfinityCategories.Sheaves.RelativeCechDiagonal
public import SerrePositivity.InfinityCategories.Sheaves.DiscretePresheafEvaluation
public import SerrePositivity.InfinityCategories.Sheaves.WeightedSectionsData
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorOpposite
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering

/-!
概要：同じ相対 Čech 対角を離散前層の全自然変換として実現し、全切断関手で読む。
方針：strictCoherentNatTransMap の同じ円柱を反対化し、元の重み付き切断を後合成する。
  文献対応：HTT 6.2.2.6 の Čech 層条件、Kerodon §2.4.3（Tag 00KM）の coherent 表示。
規約：小さい通常の site の集合値前層に特殊化する。点ごとの射の選択を集めない。
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
@[expose] public noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CatInfinity
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C] {P Q : Cᵒᵖ ⥤ Type u}

/-- 元の対角と元の Čech 増大射の全自然変換の三角形。
HTT 6.2.2.6 の通常の Čech 図式における合成の法則。 -/
lemma relativeCechDiagonal_cocone (f : P ⟶ Q) :
 relativeCechDiagonal f ≫ (relativeCechCocone f).ι =
   (Functor.const (AsSmall.{u} SimplexCategoryᵒᵖ)).map f := by
 apply NatTrans.ext
 funext j
 exact Over.w (cechPowerLift (relativeCechData f)
    (n := (AsSmall.down.obj j).unop.len) (fun _ => 𝟙 (Over.mk f)))

/-- 定値の strict な Kan 図式は同じ coherent 頂点の定値族。
Kerodon §2.4.3（Tag 00KM）、元の通常の図式の計算法則。 -/
lemma discreteStrictConstantDiagram_eq {I : Type u} [SmallCategory I] (A : KanDiagramObject Cᵒᵖ) :
 strictCoherentDiagram ((Functor.const I).obj A) = SSet.const (coherentNerveVertex A) := by
 have h : (nerveAsSmallIso I).hom ≫
      resizedNerveMap ((AsSmall.down : AsSmall.{u+1} I ⥤ I) ⋙ (Functor.const I).obj A) =
     SSet.const (nerveVertex A) := by
   apply SSet.hom_ext
   intro n
   apply ConcreteCategory.hom_ext
   intro s
   apply CategoryTheory.Functor.ext (fun _ => rfl)
 change _ ≫ _ ≫ nerveToCoherent _ = _
 rw [← Category.assoc, h, SSet.const_comp]
 change SSet.const ((nerveToCoherent (KanDiagramObject Cᵒᵖ)).app _ (ComposableArrows.mk₀ A)) = _
 rw [nerveToCoherent_vertex]

/-- 同じ対角自然変換の全 coherent 円柱。
HTT 6.2.2.6 の Čech 図式に特殊化し、元の全自然変換と定値始域を保つ。 -/
def discreteRelativeCechDiagonalHomotopy (f : P ⟶ Q) :
 SSet.Homotopy (SSet.const (functorVertex (discretePresheaf P)))
  (strictCoherentDiagram (relativeCechDiagram f ⋙ kanDiscretePresheafFunctor C) ≫
    kanDiagramRealization Cᵒᵖ) := by
 let η := Functor.whiskerRight (relativeCechDiagonal f) (kanDiscretePresheafFunctor C)
 refine homotopyOfPrism (strictCoherentNatTransMap η ≫ kanDiagramRealization Cᵒᵖ) ?_ ?_
 · rw [← Category.assoc, strictCoherentNatTransMap_zero]
   change strictCoherentDiagram ((Functor.const (AsSmall.{u} SimplexCategoryᵒᵖ)).obj
     ((kanDiscretePresheafFunctor C).obj P)) ≫ kanDiagramRealization Cᵒᵖ = _
   rw [discreteStrictConstantDiagram_eq, SSet.const_comp]
   exact congrArg (fun x => SSet.const x)
     (kanDiagramRealization_vertex ((kanDiscretePresheafFunctor C).obj P))
 · rw [← Category.assoc, strictCoherentNatTransMap_one]

/-- 円柱の各垂直辺は元の対角成分の同じ離散前層埋め込みによる像。
Kerodon §2.4.3（Tag 00KM）、指定円柱の成分の法則。 -/
lemma discreteRelativeCechDiagonalHomotopy_component (f : P ⟶ Q) (j : AsSmall.{u} SimplexCategoryᵒᵖ) :
 (simplicialHomotopyVertexEdge (discreteRelativeCechDiagonalHomotopy f) (ULift.up (ComposableArrows.mk₀ j))).edge =
 (((nerve.edgeMk ((relativeCechDiagonal f).app j)).map (kanDiscretePresheafMap C)).edge) := by
 rw [discreteRelativeCechDiagonalHomotopy, homotopyOfPrism_vertexEdge]
 change (kanDiagramRealization Cᵒᵖ).app _ ((strictCoherentNatTransMap
    (Functor.whiskerRight (relativeCechDiagonal f) (kanDiscretePresheafFunctor C))).app _ _) = _
 rw [strictCoherentNatTransMap_component]
 change (kanDiagramRealization Cᵒᵖ).app (Opposite.op ⦋1⦌)
   ((nerveToCoherent (KanDiagramObject Cᵒᵖ)).app (Opposite.op ⦋1⦌)
    (ComposableArrows.mk₁ ((kanDiscretePresheafFunctor C).map ((relativeCechDiagonal f).app j)))) = _
 change _ = (kanDiagramRealization Cᵒᵖ).app (Opposite.op ⦋1⦌)
    ((nerveToCoherent (KanDiagramObject Cᵒᵖ)).app (Opposite.op ⦋1⦌)
      ((nerveMap (kanDiscretePresheafFunctor C)).app (Opposite.op ⦋1⦌)
        (ComposableArrows.mk₁ ((relativeCechDiagonal f).app j))))
 rw [nerveMap_app_mk₁]

/-- 相対 Čech 対角の全族を、元の重み付き切断関手により反変に読む。
HTT 6.2.2.6、小さい通常の site の集合値前層と presentable 係数に特殊化する。
元の対角の円柱を一度だけ実現し、各点で選んだ射を束ねる操作は使わない。 -/
@[cite HTT "6.2.2.6" (partial := special)
  "小さい通常の site の相対 Čech 対角を presentable 係数の全切断で読む構成。"]
def weightedSections_relativeCechDiagonalHom (f : P ⟶ Q) {E : SSet.{u+1}} [Quasicategory E]
 (O : Presheaf C E)
 (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E) :
 FunctorHom
  (opFunctor.map (strictCoherentDiagram (relativeCechDiagram f ⋙ kanDiscretePresheafFunctor C) ≫
    kanDiagramRealization Cᵒᵖ) ≫ weightedSections O hE)
  (SSet.const ((weightedSections O hE).app _
    (opObjEquiv.symm (functorVertex (discretePresheaf P))))) := by
 let H := homotopyOpposite (discreteRelativeCechDiagonalHomotopy f)
 have H' := functorHomotopyPostcomp H (weightedSections O hE)
 let K := (SSet.uliftFunctor.{u+1,u}).obj (nerve (AsSmall.{u} SimplexCategoryᵒᵖ))
 have h : opFunctor.map (SSet.const (functorVertex (discretePresheaf P)) : K ⟶ _) ≫ weightedSections O hE =
    SSet.const ((weightedSections O hE).app _
     (opObjEquiv.symm (functorVertex (discretePresheaf P)))) := by
   change (SSet.const (opObjEquiv.symm (functorVertex (discretePresheaf P))) : K.op ⟶ _) ≫ _ = _
   rw [SSet.const_comp]
 have a := Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H')
 rw [h] at a
 exact a
end SerrePositivity.InfinityCategories.Sheaves
