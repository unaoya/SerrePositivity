module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictDiagramFreeArrowFrame

/-!
概要：自由frameの全族のHomを、同じHom要素圏上の実係数と自然に同定する。
方針：自由・評価随伴のHom同型を束ね、余積の挿入と元の図式射の自然性で照合する。
規約：同型は全単体と全添字射について成立する。
使われ方：HTT 4.2.4.4のRR02(a)、重み付き実現のHomと実係数の接続。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits SSet
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A] (d : StrictDiagramDirection)
local instance : ∀ (i j : strictDiagramIndex d),
    HasCoproductsOfShape (i ⟶ j) (Complex A) :=
  fun _ _ => HomologicalComplex.instHasColimitsOfShape
local instance : HomotopicalAlgebra.ModelCategory (StrictComplexDiagram A d) :=
  strictDiagramReedyModelCategory A d

/-- 同じ自由frameの全族から指定標的への実Hom図式。 -/
def strictDiagramFreeArrowHom (X Y : StrictComplexDiagram A d) :
    StrictDiagramArrowElements.{u} d ⥤ SSet.{u} :=
  (strictDiagramFreeArrowFrame A d X).rightOp ⋙
    CosimplicialHom.cosimplicialHomBifunctor.flip.obj (strictDiagramFibrantTarget A d Y)

/-- 各値の随伴同型は、全添字射の前後合成と両立する。 -/
lemma strictDiagramFreeArrowHomIso_naturality (X Y : StrictComplexDiagram A d)
    {t s : StrictDiagramArrowElements.{u} d} (g : t ⟶ s) :
    (strictDiagramFreeArrowHom A d X Y).map g ≫ (strictDiagramFreeArrowHomIso A d X Y s).hom =
      (strictDiagramFreeArrowHomIso A d X Y t).hom ≫
        (strictDiagramFrameArrowDiagram A d X Y).map g := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro f
  simp only [strictDiagramFreeArrowHom, strictDiagramFreeArrowHomIso,
    strictDiagramFreeValueHomIso, strictDiagramFreeAtAdjunction,
    CosimplicialHom.adjunctionHomIsoSameUniverse]
  change Sigma.ι (fun _ : AsSmall.down.obj s.obj.2 ⟶ AsSmall.down.obj s.obj.2 =>
      ((strictDiagramSourceFrame A d X).obj.obj n.unop).obj (AsSmall.down.obj s.obj.1.unop))
      (𝟙 (AsSmall.down.obj s.obj.2)) ≫
      (((strictDiagramFreeArrowFrame A d X).map g.op).app n.unop).app
        (AsSmall.down.obj s.obj.2) ≫ f.app (AsSmall.down.obj s.obj.2) =
    ((strictDiagramSourceFrame A d X).obj.obj n.unop).map (AsSmall.down.map g.hom.1.unop) ≫
      (Sigma.ι (fun _ : AsSmall.down.obj t.obj.2 ⟶ AsSmall.down.obj t.obj.2 =>
        ((strictDiagramSourceFrame A d X).obj.obj n.unop).obj (AsSmall.down.obj t.obj.1.unop))
        (𝟙 (AsSmall.down.obj t.obj.2)) ≫ f.app (AsSmall.down.obj t.obj.2)) ≫
        (strictDiagramFibrantTarget A d Y).map (AsSmall.down.map g.hom.2)
  simp [strictDiagramFreeArrowFrame, strictDiagramFreeArrowIndex,
    strictDiagramFreeValueFrameFamily, strictDiagramFreeAtFunctor,
    strictDiagramFreeAtReindex, strictDiagramFreeAt, strictDiagramEvaluatedSourceFrames,
    Category.assoc,
    ← f.naturality]

/-- 元の実係数と自由frameのHomの、全添字に自然な実同型。 -/
def strictDiagramFreeArrowHomNatIso (X Y : StrictComplexDiagram A d) :
    strictDiagramFreeArrowHom A d X Y ≅ strictDiagramFrameArrowDiagram A d X Y :=
  NatIso.ofComponents (strictDiagramFreeArrowHomIso A d X Y)
    (fun g => strictDiagramFreeArrowHomIso_naturality A d X Y g)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
