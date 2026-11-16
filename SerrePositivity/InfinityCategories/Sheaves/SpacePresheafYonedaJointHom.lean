module

public import SerrePositivity.InfinityCategories.Sheaves.SpacePresheafYonedaRealization
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.OrdinaryHomJointRealization

/-!
概要：固定 Yoneda の全族の実現と、通常の共同 Hom の全実現の添字を揃える。
方針：通常の Yoneda と co-Yoneda の Hom の合成則を比較し、既存の共同実現を制限する。
  文献対応：HTT 5.1.5.6、Kerodon Proposition 8.1.1.10（Tag 03JN）、固定 Yoneda の全族比較。
規約：同じ二変数の関手の等式を保持し、頂点ごとの比較へ弱めない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
open SerrePositivity.InfinityCategories.Project.SetWeightedTensors
namespace SerrePositivity.InfinityCategories.Sheaves
variable (C : Type u) [SmallCategory C]

/-- 通常の Yoneda の離散 Kan 族を uncurry すると、同じ共同 Hom の変数交換になる。
HTT 5.1.5.6、Kerodon Proposition 8.1.1.10（Tag 03JN）、全 Hom の係数移送則。 -/
lemma kanSetYonedaFamily_uncurry :
    Functor.uncurry.obj (kanSetYonedaFamily C) =
      CategoryTheory.Prod.swap C Cᵒᵖ ⋙ ordinaryHomBifunctor C ⋙ setsToKan := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro X Y f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  change setsToKan.map ((yoneda.map f.1).app X.2) ≫
      setsToKan.map ((yoneda.obj Y.1).map f.2) =
    setsToKan.map ((ordinaryHomBifunctor C).map (X := (X.2, X.1)) (Y := (Y.2, Y.1)) (f.2, f.1))
  rw [← setsToKan.map_comp]
  apply setsToKan.congr_map
  apply ConcreteCategory.hom_ext
  intro g
  exact (Category.assoc _ _ _).symm

/-- 全族の二つの持ち上げた添字を元の共同 Hom の通常の積添字へ移す。
HTT 5.1.5.6、Kerodon Proposition 8.1.1.10（Tag 03JN）、既存の積同型と変数交換の合成。 -/
def ordinaryHomFamilyBase :
    (SSet.uliftFunctor.{u + 1, u}).obj (nerve Cᵒᵖ) ⊗
        (SSet.uliftFunctor.{u + 1, u}).obj (nerve C) ⟶
      (SSet.uliftFunctor.{u + 1, u}).obj (nerve (Cᵒᵖ × C)) :=
  (uliftNerveProductSwapIso C Cᵒᵖ).inv ≫
    (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (CategoryTheory.Prod.swap C Cᵒᵖ))

/-- 固定 Yoneda の指定射は同じ共同 Hom の全実現を curry した射である。
HTT 5.1.5.6、Kerodon Proposition 8.1.1.10（Tag 03JN）、元の射を保つ全族の係数移送。 -/
lemma liftedSetYoneda_jointHom_curry :
    liftedSetYoneda C ≫ (discretePresheafInclusion C).val =
      curry (ordinaryHomFamilyBase C ≫ spaceDiagram (ordinaryHomBifunctor C)) := by
  rw [liftedSetYoneda_realization_curry, kanSetYonedaFamily_uncurry]
  change curry (_ ≫ kanDiagramCoherentNerve
    (CategoryTheory.Prod.swap C Cᵒᵖ ⋙ (ordinaryHomBifunctor C ⋙ setsToKan))) = _
  rw [← kanDiagramCoherentNerve_precomp, ← Category.assoc]
  rfl

end SerrePositivity.InfinityCategories.Sheaves
