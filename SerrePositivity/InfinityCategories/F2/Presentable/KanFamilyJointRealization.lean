module

public import SerrePositivity.InfinityCategories.F2.Presentable.KanDiagramBundle
public import SerrePositivity.InfinityCategories.F2.Ind.NerveProductSwapIso
public import Mathlib.CategoryTheory.Functor.Currying

/-!
概要：束縛した strict Kan 図式族の全実現は、元の積図式の全実現を curry したものに一致する。
方針：全順序 path の混合 Hom を元の自然変換と輸送の合成へ戻し、全単体で共同評価する。
規約：頂点だけでなく、元の全高次を厳密に保持する。
使われ方：実現した strict 余極限余錐を、共同 strictification の元の族上に公開する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits Ind
variable {I J L : Type u} [SmallCategory I] [SmallCategory J] [LinearOrder L]
  (F : J ⥤ I ⥤ KanObject.{u})

/-- 同じ二つの順序図式の対角評価は、元の通常の積図式の全実現である。 -/
lemma kanFamily_diagonal_realization (Q : L ⥤ J) (R : L ⥤ I) :
    diagonalKanDiagramEvaluation R
      (enrichedFunctorOfOrderDiagram (Q ⋙ F ⋙ kanDiagramBundle)) =
      enrichedFunctorOfOrderDiagram (Q.prod' R ⋙ CategoryTheory.Functor.uncurry.obj F) := by
  refine EnrichedFunctor.ext SSet (fun _ ↦ rfl) ?_
  intro i j
  simp only [eqToHom_refl, Category.comp_id]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro P
  have hij := SimplicialThickening.Path.le (P.obj 0)
  change (diagonalKanDiagramHom R
    (enrichedFunctorOfOrderDiagram (Q ⋙ F ⋙ kanDiagramBundle)) i j).app n P = _
  rw [diagonalKanDiagramHom_of_le _ _ i j hij]
  change (strictDiagramMixedHom (R.map (homOfLE hij))
      ((F.obj (Q.obj i.as)) ⋙ kanObjectForget)
      ((F.obj (Q.obj j.as)) ⋙ kanObjectForget)).app n
    (PinchedHom.constant (SimplicialCategory.homEquiv' (C := KanDiagramObject I)
      (⟨F.obj (Q.obj i.as), trivial⟩ : KanDiagramObject I)
      (⟨F.obj (Q.obj j.as), trivial⟩ : KanDiagramObject I)
      (kanDiagramHom (C := I) (F := ⟨F.obj (Q.obj i.as), trivial⟩)
        (G := ⟨F.obj (Q.obj j.as), trivial⟩)
        (Functor.whiskerRight (F.map (Q.map (homOfLE hij))) kanObjectForget)))
        n.unop.len) = _
  rw [pinchedConstant_map, kanDiagramHom_vertex]
  congr 1

/-- 元の積図式の共同実現は、束縛した同じ図式族の実現の共同評価と全単体で一致する。 -/
lemma kanFamily_joint_realization :
    lift ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (CategoryTheory.Prod.snd J I)))
      ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (CategoryTheory.Prod.fst J I)) ≫
        strictCoherentDiagram (F ⋙ kanDiagramBundle)) ≫ kanDiagramJointEvaluation I =
      kanDiagramCoherentNerve (CategoryTheory.Functor.uncurry.obj F) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨σ⟩
  let d := (⟨ULift.down, fun _ _ h ↦ h⟩ :
    ULift.{u} (Fin (n + 1)) →o Fin (n + 1)).toFunctor
  exact kanFamily_diagonal_realization F
    (d ⋙ σ ⋙ CategoryTheory.Prod.fst J I) (d ⋙ σ ⋙ CategoryTheory.Prod.snd J I)

/-- 実現した全図式族は、元の積添字の全実現の curry と厳密に一致する。 -/
lemma kanFamily_realization_curry :
    strictCoherentDiagram (F ⋙ kanDiagramBundle) ≫ kanDiagramRealization I =
      curry ((uliftNerveProductSwapIso J I).inv ≫
        kanDiagramCoherentNerve (CategoryTheory.Functor.uncurry.obj F)) := by
  apply uncurry_injective
  rw [uncurry_natural_left, kanDiagramRealization, uncurry_curry, uncurry_curry,
    ← kanFamily_joint_realization F]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro σ
  rfl

end SerrePositivity.InfinityCategories.F2.Presentable
