module

public import SerrePositivity.InfinityCategories.Sheaves.PresheafRelativeCechHom
public import SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetCoconeCoefficientIso

/-!
概要：各点で全射な前層の同じ Čech 増大は、元の点で評価した空間値余極限余錐になる。
方針：既存 curriedYonedaLemma の全自然同型を、元の増大を保つ係数移送に適用する。
規約：HTT 6.2.2.6 の Čech 解消への入力。各点の同型を選んで大域比較を組み立てない。
使われ方：S8 の像への全射の Čech 解消。元の商の頂点と全ての増大の脚を保持する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
open SerrePositivity.InfinityCategories.Project.SetWeightedTensors
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C] {P Q : Cᵒᵖ ⥤ Type u}

/-- 同じ各点での全射の Čech 余錐を、その点でそのまま評価した native な余極限性。 -/
lemma presheafRelativeCechEvaluation_isColimit (f : P ⟶ Q)
    (hf : ∀ X : Cᵒᵖ, Function.Surjective (f.app X)) (U : C) :
    IsColimitCone (strictNativeCocone (setsToKan.mapCocone
      (((evaluation Cᵒᵖ (Type u)).obj (Opposite.op U)).mapCocone (relativeCechCocone f)))) := by
  apply mappedSetCocone_isColimit_of_contractible_comma_and_iso (relativeCechCocone f)
    ((curriedYonedaLemma (C := C)).app (Opposite.op U))
  rintro ⟨r⟩
  obtain ⟨a, ha⟩ := presheafSurjective_yoneda_lift f hf U r
  exact relativeCechPointComma_isWeaklyContractible f r a ha

end SerrePositivity.InfinityCategories.Sheaves
