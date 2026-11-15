module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictDiagramFreeEvaluationElementsAugmentation
public import SerrePositivity.HomotopicalAlgebra.Diagram.FrameBousfieldKanAugmentationPost
public import SerrePositivity.HomotopicalAlgebra.Diagram.BousfieldKanAugmentationIsoTransport

/-!
概要：評価した自由frameの増大余錐の各脚を、元の合成射の像として照合する。
方針：余積挿入を指定表示同型の逆に通し、Overの終対象への射の左成分を計算する。
使われ方：HTT 4.2.4.4、RR02(a)の元の自由増大射の評価値の同定。
規約：元の評価frame、表示同型、余錐の脚を保持する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.DifferentialGraded SerrePositivity.DiagramModel
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A] (d : StrictDiagramDirection)
local instance coconeLegs_diagramModel : HomotopicalAlgebra.ModelCategory (StrictComplexDiagram A d) :=
  strictDiagramReedyModelCategory A d
local instance coconeLegs_colimits : HasColimitsOfSize.{u, u} (Complex A) :=
  ⟨fun _ _ => HomologicalComplex.instHasColimitsOfShape⟩
local instance coconeLegs_coproducts : ∀ (i j : strictDiagramIndex d),
    HasCoproductsOfShape (i ⟶ j) (Complex A) :=
  fun _ _ => HomologicalComplex.instHasColimitsOfShape

/-- 元の自由増大余錐を、そのまま指定評価点で評価する。 -/
def strictDiagramFreeEvaluationPostCocone (X : StrictComplexDiagram A d)
    (k : strictDiagramIndex d) :=
  FrameWeightRealization.postZeroCocone (StrictDiagramArrowElements.{u} d)ᵒᵖ
    (strictDiagramFreeArrowFrame A d X) (strictDiagramFreeArrowZeroCocone A d X)
    (L := (CategoryTheory.evaluation (strictDiagramIndex d) (Complex A)).obj k)

/-- 指定余積表示同型の逆で、評価余錐の脚を前合成する。 -/
def strictDiagramFreeEvaluationCopowerCocone (X : StrictComplexDiagram A d)
    (k : strictDiagramIndex d) :=
  (Cocone.precompose (ConstantWeightRealization.degreeMap _
    (strictDiagramFreeEvaluationFramesIso A d X k).inv (SimplexCategory.mk 0))).obj
      (strictDiagramFreeEvaluationPostCocone A d X k)

/-- 宇宙移送後の終対象への指定射も、左成分は元のOverの構造射。 -/
lemma strictDiagramFreeEvaluationOverTerminal_from_left (k : strictDiagramIndex d)
    (t : AsSmall.{u} (Over k)) :
    (AsSmall.down.map ((strictDiagramFreeEvaluationOverTerminal d k).from t)).left =
      (AsSmall.down.obj t).hom := by
  have h := Over.mkIdTerminal.hom_ext
    (AsSmall.down.map ((strictDiagramFreeEvaluationOverTerminal d k).from t))
    (Over.homMk (AsSmall.down.obj t).hom)
  exact congrArg Over.Hom.left h

/-- 余積の要素ごとの脚は、元の二本の射の合成の像である。 -/
lemma strictDiagramFreeEvaluationCopowerCocone_leg (X : StrictComplexDiagram A d)
    (k : strictDiagramIndex d) (e : (strictDiagramFreeEvaluationLiftedWeight.{u} d k).Elements) :
    (ElementsCopower.elementsZeroCocone (strictDiagramFreeEvaluationLiftedWeight d k)
      (strictDiagramFreeEvaluationBase A d X) (strictDiagramFreeEvaluationCopowerCocone A d X k)).ι.app e =
      ((strictDiagramSourceFrame A d X).obj.obj (SimplexCategory.mk 0)).map
        (AsSmall.down.map e.obj.unop.val ≫ e.val.down) := by
  change Sigma.ι _ e.val ≫
    (Sigma.map' ULift.down (fun _ => 𝟙 _) ≫
      Sigma.desc (fun h => ((strictDiagramSourceFrame A d X).obj.obj (SimplexCategory.mk 0)).map
        (AsSmall.down.map e.obj.unop.val ≫ h))) = _
  simp [Category.assoc]

/-- Overから制限した同じ余錐の脚も、同じ合成射の像である。 -/
lemma strictDiagramFreeEvaluationElementsCocone_leg (X : StrictComplexDiagram A d)
    (k : strictDiagramIndex d) (e : (strictDiagramFreeEvaluationLiftedWeight.{u} d k).Elements) :
    (strictDiagramFreeEvaluationElementsCocone A d X k).ι.app e =
      ((strictDiagramSourceFrame A d X).obj.obj (SimplexCategory.mk 0)).map
        (AsSmall.down.map e.obj.unop.val ≫ e.val.down) := by
  change 𝟙 _ ≫ ((strictDiagramSourceFrame A d X).obj.obj (SimplexCategory.mk 0)).map
    (AsSmall.down.map ((strictDiagramFreeEvaluationOverTerminal d k).from
      ((strictDiagramFreeEvaluationLiftedToOver d k).obj e))).left = _
  rw [Category.id_comp, strictDiagramFreeEvaluationOverTerminal_from_left]
  rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
