module

public import SerrePositivity.InfinityCategories.HomotopyLimits.GeneralConeComparisonReflection

/-!
概要：元の Bousfield–Kan end の点を、係数の edgewise 共通解像へ厳密に持ち上げる。
方針：各係数の右射影の自明 Kan fibration 性を end へ移し、初対象からの持ち上げで切断を取る。
規約：切断の源変数に関する自然性は主張しない。使われ方：元の BF 恒等射の像の反転。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open SerrePositivity.InfinityCategories SerrePositivity.InfinityCategories.HomotopyLimits
namespace SerrePositivity.KST.Spectra
variable {I : Type u} [SmallCategory I]

/-- 共通解像の右 end 射影の、実際の切断とその厳密な右逆関係。 -/
def edgewiseEndRightSectionData (H : I ⥤ SSet.{u}) [∀ i, KanComplex (H.obj i)] :
    {s : bousfieldKanHolim H ⟶ bousfieldKanHolim (H ⋙ edgewiseSubdivisionFunctor) //
      s ≫ weightedSectionsMap (bousfieldKanWeight I) (diagramEdgewiseRight H) = 𝟙 _} := by
  letI coefficientRightTrivial : ∀ i, TrivialKanFibration ((diagramEdgewiseRight H).app i) :=
    fun i ↦ edgewiseRight_trivialKanFibration (H.obj i)
  letI endRightTrivial : TrivialKanFibration
      (weightedSectionsMap (bousfieldKanWeight I) (diagramEdgewiseRight H)) :=
    bousfieldKanMap_trivialKanFibration (diagramEdgewiseRight H)
  have := TrivialKanFibration.mem
    (p := weightedSectionsMap (bousfieldKanWeight I) (diagramEdgewiseRight H))
    (initial.to (bousfieldKanHolim H)) inferInstance
  let sq : CommSq (initial.to (bousfieldKanHolim (H ⋙ edgewiseSubdivisionFunctor)))
      (initial.to (bousfieldKanHolim H))
      (weightedSectionsMap (bousfieldKanWeight I) (diagramEdgewiseRight H))
      (𝟙 (bousfieldKanHolim H)) := ⟨by apply initial.hom_ext⟩
  exact ⟨sq.lift, sq.fac_right⟩

/-- 元の end から共通解像へ取った右切断。 -/
def edgewiseEndRightSection (H : I ⥤ SSet.{u}) [∀ i, KanComplex (H.obj i)] :
    bousfieldKanHolim H ⟶ bousfieldKanHolim (H ⋙ edgewiseSubdivisionFunctor) :=
  (edgewiseEndRightSectionData H).val

/-- 右切断を元の係数へ射影すると元の end の恒等射。 -/
lemma edgewiseEndRightSection_projection (H : I ⥤ SSet.{u}) [∀ i, KanComplex (H.obj i)] :
    edgewiseEndRightSection H ≫
      weightedSectionsMap (bousfieldKanWeight I) (diagramEdgewiseRight H) = 𝟙 _ :=
  (edgewiseEndRightSectionData H).property

end SerrePositivity.KST.Spectra
