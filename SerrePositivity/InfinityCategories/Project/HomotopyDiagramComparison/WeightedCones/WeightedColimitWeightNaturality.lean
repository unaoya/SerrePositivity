module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.WeightedCones.WeightedColimitWeightTransport

/-!
概要：指定重みの同型による coend の移送は、元の係数図式の射に自然。
方針：同じ普遍脚の式と既存 tensor の交換則を使う。
規約：Kerodon §7.5.1（Tag 03A0）の既存の重み模型の係数移送の法則。
使われ方：Čech の元の増大を反転 BK と元の圏の比較で保つ。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
variable {I : Type u} [SmallCategory I]

/-- 同じ重みの指定同型の像は、係数図式の全自然変換と可換。 -/
lemma weightedColimitWeightIso_naturality {W V : Iᵒᵖ ⥤ SSet.{u}}
    (e : W ≅ V) {F G : I ⥤ SSet.{u}} (η : F ⟶ G) :
    weightedColimitMap W η ≫ (weightedColimitWeightIso e G).hom =
      (weightedColimitWeightIso e F).hom ≫ weightedColimitMap V η := by
  apply weightedColimit_hom_ext
  intro i
  calc
    _ = η.app i ▷ W.obj (Opposite.op i) ≫
        (weightedColimitι W G i ≫ (weightedColimitWeightIso e G).hom) := by
      rw [← Category.assoc, weightedColimitι_map, Category.assoc]
    _ = η.app i ▷ W.obj (Opposite.op i) ≫ G.obj i ◁ e.hom.app (Opposite.op i) ≫
        weightedColimitι V G i := by rw [weightedColimitWeightIso_ι_hom]
    _ = F.obj i ◁ e.hom.app (Opposite.op i) ≫ η.app i ▷ V.obj (Opposite.op i) ≫
        weightedColimitι V G i := by rw [whisker_exchange_assoc]
    _ = _ := by
      rw [← weightedColimitι_map]
      simpa only [Category.assoc] using
        (congrArg (fun t => t ≫ weightedColimitMap V η)
          (weightedColimitWeightIso_ι_hom e F i)).symm

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
