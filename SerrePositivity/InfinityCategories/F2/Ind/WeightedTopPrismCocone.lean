module

public import SerrePositivity.InfinityCategories.F2.Ind.WeightedTopPrism

/-!
概要：weighted 全空間の最大添字への円柱は、元の定値余錐への評価を厳密に保つ。
方針：最後の係数の輸送を同じ余錐の自然性で消去する。
規約：余極限性や係数の充填性は不要。使われ方：元の全空間余極限上での相対収縮。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 最大添字への全輸送の間、元の定値余錐への評価は厳密に定値。 -/
lemma weightedTopPrism_cocone {I : Type u} [PartialOrder I] [OrderTop I]
    (F : I ⥤ SSet.{u}) {Y : SSet.{u}} (η : F ⟶ (CategoryTheory.Functor.const I).obj Y) :
    weightedTopPrism F ≫ (weightedNerveMap η ≫ weightedNerveConstantEvaluation I Y) =
      snd (Δ[1] : SSet.{u}) (weightedNerve F) ≫
        (weightedNerveMap η ≫ weightedNerveConstantEvaluation I Y) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨t, s⟩
  change weightedNerveSimplex F n at s
  change SSet.yonedaEquiv ((s.2.app (Fin.last n) ≫
      F.map (homOfLE (le_weightedTopChain s.1 (stdSimplex.objEquiv t).toOrderHom (Fin.last n)))) ≫
      η.app ((weightedTopChain s.1 (stdSimplex.objEquiv t).toOrderHom).obj (Fin.last n))) =
    SSet.yonedaEquiv (s.2.app (Fin.last n) ≫ η.app (s.1.obj (Fin.last n)))
  apply congrArg SSet.yonedaEquiv
  exact (Category.assoc _ _ _).trans (congrArg (fun q => s.2.app (Fin.last n) ≫ q)
    ((η.naturality (homOfLE (le_weightedTopChain s.1 (stdSimplex.objEquiv t).toOrderHom
      (Fin.last n)))).trans (Category.comp_id _)))

end SerrePositivity.InfinityCategories.F2.Ind
