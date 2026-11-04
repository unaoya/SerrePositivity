module
public import SerrePositivity.InfinityCategories.Stable.KanModels.KanCommSqLimit
public import SerrePositivity.KST.Fibration.KanCommSqCone

/-! # 元の Kan homotopy pullback 四角形を、同じ全 coherent 極限錐へ移す -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.InfinityCategories.HomotopyLimits
open SerrePositivity.KST.Comparison
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration

/-- 任意の元の Kan homotopy pullback 四角形は、そのまま coherent な実極限錐を与える。 -/
theorem kanCommSqCone_isLimit {P X Y Z : KanObject.{u}}
    {a : P.obj ⟶ X.obj} {b : P.obj ⟶ Y.obj} {f : X.obj ⟶ Z.obj} {g : Y.obj ⟶ Z.obj}
    (sq : CommSq a b f g) (hsq : IsHomotopyPullback sq) :
    IsLimitCone (strictCoherentCone (kanCommSqCone sq)) := by
  let R := kanCommSqReplacementTarget g
  let p : R ⟶ Z := AnodyneKanReplacement.factorization.p.app (Arrow.mk g)
  let i : Y ⟶ R := AnodyneKanReplacement.factorization.i.app (Arrow.mk g)
  have fac : (show Y.obj ⟶ R.obj from i) ≫ p = g :=
    AnodyneKanReplacement.factorization.fac_app
  have : Fibration (show R.obj ⟶ Z.obj from p) :=
    (SSet.modelCategoryQuillen.fibration_iff _).mpr
      (AnodyneKanReplacement.factorization.hp _)
  have hQi : IsIso (AnodyneHomotopy.anodyneQ.map (show Y.obj ⟶ R.obj from i)) :=
    (Localization.inverts AnodyneHomotopy.anodyneQ anodyneExtensions) _
      (AnodyneKanReplacement.factorization.hi _)
  have sq' : CommSq a (b ≫ i) f (show R.obj ⟶ Z.obj from p) := by
    constructor
    rw [Category.assoc, fac]
    exact sq.w
  have hsq' : IsHomotopyPullback sq' := by
    apply (isHomotopyPullback_iff_of_localized_isIso sq sq'
      (𝟙 P.obj) (𝟙 X.obj) (show Y.obj ⟶ R.obj from i) (𝟙 Z.obj)
      (by simp) (by simp) (by simp) ?_
      (by infer_instance) (by infer_instance) hQi (by infer_instance)).mp hsq
    simpa only [Category.comp_id] using fac.symm
  let α : NatTrans (kanPullbackDiagram (show Y ⟶ Z from g) (show X ⟶ Z from f))
      (kanPullbackDiagram p (show X ⟶ Z from f)) :=
    Functor.whiskerLeft AsSmall.down
      (cospanHomMk (𝟙 Z) i (𝟙 X) (by
        change g ≫ 𝟙 Z.obj = (show Y.obj ⟶ R.obj from i) ≫ p
        exact (Category.comp_id g).trans fac.symm) (by
        change f ≫ 𝟙 Z.obj = 𝟙 X.obj ≫ f
        simp only [Category.comp_id, Category.id_comp]))
  have hi : IsInvertibleEdge (coherentNerveEdge i) :=
    coherentKanEdge_isInvertible_of_isQCatEquivalence (isQCatEquivalence_of_anodyneQ_isIso i hQi)
  have hα : ∀ j, IsInvertibleEdge (coherentNerveEdge (α.app j)) := by
    intro j
    rcases j with ⟨_ | (_ | _)⟩
    · exact kanIdentityEdge_isInvertible Z
    · exact hi
    · exact kanIdentityEdge_isInvertible X
  have hid : IsInvertibleEdge (coherentNerveEdge (𝟙 P)) := kanIdentityEdge_isInvertible P
  apply (strictCoherentCone_isLimit_iff_of_transformation α
    (kanCommSqCone sq) (kanCommSqCone (P := P) (X := X) (Y := R) (Z := Z) sq')
    (𝟙 P) ?_ hα hid).mpr
  · exact kanCommSqCone_isLimit_of_fibration sq' hsq'
  · intro j
    rcases j with ⟨_ | (_ | _)⟩
    · change 𝟙 P.obj ≫ ((b ≫ i) ≫ p) = (b ≫ g) ≫ 𝟙 Z.obj
      simp only [Category.id_comp, Category.comp_id, Category.assoc, fac]
    · change 𝟙 P.obj ≫ (b ≫ i) = b ≫ i
      exact Category.id_comp _
    · change 𝟙 P.obj ≫ a = a ≫ 𝟙 X.obj
      simp only [Category.id_comp, Category.comp_id]

end SerrePositivity.KST.Fibration
