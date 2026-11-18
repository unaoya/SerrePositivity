module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.WeightedCones.WeightedColimit

/-!
概要：同じ重み付き coend を、指定した重みの自然同型に沿って移す。
方針：既存の tensor と coendFunctor の同型の像を使い、各普遍脚の式を保持する。
規約：Kerodon §7.5.1（Tag 03A0）の既存の重み模型の係数移送の法則。
使われ方：反転 BK 重みと Under 重みを、同じ図式と増大を保って比較する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
variable {I : Type u} [SmallCategory I]

/-- 固定した係数図式に対する、既存の重みの coend 関手。 -/
def weightedColimitWeightFunctor (F : I ⥤ SSet.{u}) :
    (Iᵒᵖ ⥤ SSet.{u}) ⥤ SSet.{u} :=
  (Functor.whiskeringRight Iᵒᵖ SSet.{u} (I ⥤ SSet.{u})).obj
    ((curriedTensor SSet.{u}).flip ⋙
      (Functor.whiskeringLeft I SSet.{u} SSet.{u}).obj F) ⋙ coendFunctor I SSet.{u}

/-- 重みの指定自然同型を、同じ coend の自然同型へ送る。 -/
def weightedColimitWeightIso {W V : Iᵒᵖ ⥤ SSet.{u}}
    (e : W ≅ V) (F : I ⥤ SSet.{u}) : weightedColimit W F ≅ weightedColimit V F :=
  (weightedColimitWeightFunctor F).mapIso e

/-- 同じ順方向の同型は、各普遍脚で指定された重みの同型そのものを使う。 -/
lemma weightedColimitWeightIso_ι_hom {W V : Iᵒᵖ ⥤ SSet.{u}}
    (e : W ≅ V) (F : I ⥤ SSet.{u}) (i : I) :
    weightedColimitι W F i ≫ (weightedColimitWeightIso e F).hom =
      F.obj i ◁ e.hom.app (Opposite.op i) ≫ weightedColimitι V F i :=
  coend.ι_map _ i

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
