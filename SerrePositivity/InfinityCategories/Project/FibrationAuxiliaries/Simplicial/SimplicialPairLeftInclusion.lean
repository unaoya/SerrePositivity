module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.SimplicialPairNerve

/-!
概要：第二の対象を固定した豊穣積の包含と、その coherent nerve の計算。
方針：第一の Hom を保ち、第二の Hom に恒等射を入れる。
規約：両圏の充填性は要求しない。
使われ方：二変数の Hom の共同評価をテスト標的で評価する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial

/-- 第二の対象を固定し、第一の対象の全高次の射を積の豊穣圏へ含める。 -/
def simplicialPairLeftInclusion (C : Type v) [Category.{u} C] [SimplicialCategory C]
    {D : Type v} [Category.{u} D] [SimplicialCategory D] (Y : D) :
    EnrichedFunctor SSet.{u} C (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.SimplicialPairObject C D) where
  obj X := (X, Y)
  map X Z := lift (𝟙 _) (toUnit (SimplicialCategory.sHom X Z) ≫ eId SSet Y)
  map_id _X := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro t
    rfl
  map_comp _X _Z _W := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    rintro ⟨f, g⟩
    apply Prod.ext
    · rfl
    · exact (congrArg (fun k ↦ k.app n ((eId SSet Y).app n PUnit.unit))
        (e_id_comp SSet Y Y)).symm

/-- 第二の頂点を固定した積の包含は、豊穣包含の coherent nerve。 -/
lemma simplicialPairNerveFrom_left {C D : Type v}
    [Category.{u} C] [SimplicialCategory C] [Category.{u} D] [SimplicialCategory D]
    (Y : D) :
    lift (𝟙 (SimplicialNerve C)) (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex Y)) ≫
      _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.simplicialPairNerveFrom C D = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (simplicialPairLeftInclusion C Y) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro F
  apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
  intro i j
  simp only [eqToHom_refl, Category.comp_id]

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial
