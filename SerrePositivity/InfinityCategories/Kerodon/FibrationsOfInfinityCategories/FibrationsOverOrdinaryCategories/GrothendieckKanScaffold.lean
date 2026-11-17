module
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.GrothendieckKanCoefficientLift
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.NerveCocartesianScaffold
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialReplacementFunctor
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PrecompositionTensor

/-!
概要：元のCat係数のtaut scaffoldを同じGrothendieck射列へ接続する。
方針：R03eの逆射を後合成し、元の係数の単位との可換性をscaffold自然性から得る。
規約：nerve係数のquasicategory性を用い、Kan性を仮定しない。
使われ方：IS-W2 R03fの元の射を保つbar/scaffold比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
variable {I : Type u} [SmallCategory I] (F : I ⥤ Cat.{u,u})

/-- 元のnerve係数のbarから、同じGrothendieck射列へのscaffold。 -/
def grothendieckNerveScaffold :
    simplicialReplacement (F ⋙ nerveFunctor) ⟶ nerve (Grothendieck F) :=
  tautScaffold (F ⋙ nerveFunctor) ≫ (grothendieckWeightedNerveIso F).inv

/-- 同じscaffoldは、元の同じ底への射影を保つ。 -/
theorem grothendieckNerveScaffold_projection :
    grothendieckNerveScaffold F ≫ nerveMap (Grothendieck.forget F) =
      simplicialReplacementProjection (F ⋙ nerveFunctor) := by
  have hi : (grothendieckWeightedNerveIso F).inv ≫ nerveMap (Grothendieck.forget F) =
      weightedNerveProjection (F ⋙ nerveFunctor) := by
    rw [← grothendieckWeightedNerveIso_projection F, ← Category.assoc,
      Iso.inv_hom_id, Category.id_comp]
  rw [grothendieckNerveScaffold, Category.assoc, hi, tautScaffold_projection]

/-- 元のnerve係数のscaffoldは、全空間の前合成同値である。 -/
theorem grothendieckNerveScaffold_isPrecompositionEquivalence :
    IsPrecompositionEquivalence (grothendieckNerveScaffold F) := by
  haveI : ∀ i : I, Quasicategory ((F ⋙ nerveFunctor).obj i) := fun i => by
    change Quasicategory (nerve (F.obj i))
    infer_instance
  exact (tautScaffold_isPrecompositionEquivalence_of_quasicategory (F ⋙ nerveFunctor)).comp
    (isPrecompositionEquivalence_of_iso (grothendieckWeightedNerveIso F).symm)

/-- 元の係数の単位への比較は、同じbarの自然変換と厳密に可換する。 -/
theorem grothendieckNerveScaffold_kanCoefficientMap :
    grothendieckNerveScaffold F ≫ grothendieckKanCoefficientMap F =
      simplicialReplacementMap (grothendieckKanCoefficientUnit F) ≫
        tautScaffold (grothendieckKanCoefficients F) := by
  have hi : (grothendieckWeightedNerveIso F).inv ≫ grothWeightedNerveForward F = 𝟙 _ := by
    simpa only [grothendieckWeightedNerveIso, asIso_hom] using
      (grothendieckWeightedNerveIso F).inv_hom_id
  rw [grothendieckNerveScaffold, grothendieckKanCoefficientMap, Category.assoc,
    ← Category.assoc (grothendieckWeightedNerveIso F).inv, hi, Category.id_comp]
  exact (tautScaffold_map (grothendieckKanCoefficientUnit F)).symm

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
