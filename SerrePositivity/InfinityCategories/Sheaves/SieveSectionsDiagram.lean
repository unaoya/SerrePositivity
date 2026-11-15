module

public import SerrePositivity.InfinityCategories.Sheaves.SieveElements
public import SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetSections

/-!
概要：篩の切断図式は、要素圏の指定同値で制限図式へ戻る。
方針：基底への射影保存とnerve・宇宙持ち上げの合成則を使う。
使われ方：HTT 6.2.2.6、Kerodon §7.1（Tag 02H1）の層条件の切断表示。
規約：G8で使う元の図式を再利用する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory
open SerrePositivity.InfinityCategories.Project.SetWeightedTensors
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C] {E : SSet.{u+1}}

/-- 元の集合重みの切断図式を、同じ前層から読む。 -/
abbrev sectionsOfDiagram (P : Cᵒᵖ ⥤ Type u) (F : Presheaf C E) :=
  SetWeight.diagram P F

/-- 包含を経由した表現可能前層の射影も元の篩図式。 -/
lemma sieveCategoryToElements_inclusion_comp_π {U : C} (S : Sieve U) :
    sieveCategoryToElements S ⋙ S.functorInclusion.mapElements ⋙
      Functor.Elements.π (yoneda.obj U) = sieveDiagram S := rfl

/-- 指定した再添字によって元の制限図式と厳密に一致する。 -/
lemma sieveSectionsDiagram_reindex {U : C} (S : Sieve U) (F : Presheaf C E) :
    (SSet.uliftFunctor.{u+1,u}).map (nerveMap (sieveCategoryToElements S)) ≫
      sectionsOfDiagram S.functor F = restriction F S := by
  dsimp only [sectionsOfDiagram, SetWeight.diagram, SetWeight.projection, restriction]
  rw [← Category.assoc, ← CategoryTheory.Functor.map_comp]
  rfl

end SerrePositivity.InfinityCategories.Sheaves
