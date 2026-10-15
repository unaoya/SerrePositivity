module

public import SerrePositivity.HomotopicalAlgebra.Smith.AccessibleColimits
public import Mathlib.CategoryTheory.SmallObject.TransfiniteIteration

/-! # Accessibility of the existing transfinite-iteration construction

Once a successor endofunctor is accessible at a fixed regular cardinal,
Mathlib's actual iteration of its unit is accessible at that same cardinal.
The cell-attachment successor used by the small-object argument must still
be proved accessible separately.
-/

@[expose] public section
universe w v u v' u'
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.SmallObject

namespace SerrePositivity.Smith.AccessibleIteration
variable {C : Type u} [Category.{v} C] [HasColimitsOfSize.{w, w} C]
  {D : Type u'} [Category.{v'} D]
  {J : Type w} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]

lemma stages_isCardinalAccessible (F : J ⥤ D ⥤ C) [F.IsWellOrderContinuous]
    (κ : Cardinal.{w}) [Fact κ.IsRegular]
    (hbot : (F.obj ⊥).IsCardinalAccessible κ)
    (hsucc : ∀ j, ¬IsMax j → (F.obj j).IsCardinalAccessible κ →
      (F.obj (Order.succ j)).IsCardinalAccessible κ) (j : J) :
    (F.obj j).IsCardinalAccessible κ := by
  induction j using SuccOrder.limitRecOn with
  | isMin j hj =>
    have h : j = ⊥ := by simpa only [isMin_iff_eq_bot] using hj
    subst j
    exact hbot
  | succ j hj ih => exact hsucc j hj ih
  | isSuccLimit j hj ih =>
    let G := (Set.principalSegIio j).monotone.functor ⋙ F
    have : ∀ k, (G.obj k).IsCardinalAccessible κ := fun k ↦ ih k.val k.property
    have : (colimit.cocone G).pt.IsCardinalAccessible κ :=
      AccessibleColimits.colimit_isCardinalAccessible G κ
    exact Functor.isCardinalAccessible_of_natIso
      ((colimit.isColimit G).coconePointUniqueUpToIso
        (F.isColimitOfIsWellOrderContinuous j hj)) κ

variable (T : C ⥤ C) (ε : 𝟭 C ⟶ T) (κ : Cardinal.{w}) [Fact κ.IsRegular]
  [T.IsCardinalAccessible κ]

lemma iterationStage_isCardinalAccessible (j : J) :
    (((SuccStruct.ofNatTrans ε).iterationFunctor J).obj j).IsCardinalAccessible κ := by
  apply stages_isCardinalAccessible _ κ
  · have : (SuccStruct.ofNatTrans ε).X₀.IsCardinalAccessible κ :=
      inferInstanceAs ((𝟭 C).IsCardinalAccessible κ)
    exact Functor.isCardinalAccessible_of_natIso
      ((SuccStruct.ofNatTrans ε).iterationFunctorObjBotIso J).symm κ
  · intro j hj ih
    have := ih
    have : (((SuccStruct.ofNatTrans ε).iterationFunctor J).obj j ⋙ T).IsCardinalAccessible κ :=
      inferInstance
    have : ((SuccStruct.ofNatTrans ε).succ
        (((SuccStruct.ofNatTrans ε).iterationFunctor J).obj j)).IsCardinalAccessible κ :=
      inferInstanceAs
        ((((SuccStruct.ofNatTrans ε).iterationFunctor J).obj j ⋙ T).IsCardinalAccessible κ)
    exact Functor.isCardinalAccessible_of_natIso
      ((SuccStruct.ofNatTrans ε).iterationFunctorObjSuccIso j hj).symm κ

lemma iteration_isCardinalAccessible :
    ((SuccStruct.ofNatTrans ε).iteration J).IsCardinalAccessible κ := by
  have := fun j : J ↦ iterationStage_isCardinalAccessible T ε κ j
  exact AccessibleColimits.colimit_isCardinalAccessible
    ((SuccStruct.ofNatTrans ε).iterationFunctor J) κ

end SerrePositivity.Smith.AccessibleIteration
