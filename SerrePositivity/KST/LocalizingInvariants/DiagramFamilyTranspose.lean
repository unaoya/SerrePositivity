module

public import SerrePositivity.KST.LocalizingInvariants.ZeroArrowFamily
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomSquare
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.PointFunctorEvaluation

/-!
概要：図式の全族を、関手圏内の一つの図式へ転置する。
方針：直積の対称性と curry を使い、辺への制限も厳密に比較する。
規約：パラメータは任意の単体集合。使われ方：cofiber 全族の h Fun 内の零合成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

/-- A 上の K 図式の族を、Fun(A,X) 内の K 図式にする。 -/
def diagramFamilyTranspose {A K X : SSet.{u}} (f : A ⟶ (ihom K).obj X) :
    K ⟶ (ihom A).obj X := curry ((β_ A K).hom ≫ uncurry f)

lemma diagramFamilyTranspose_pre {A K L X : SSet.{u}}
    (f : A ⟶ (ihom K).obj X) (i : L ⟶ K) :
    i ≫ diagramFamilyTranspose f = diagramFamilyTranspose (f ≫ (pre i).app X) := by
  apply uncurry_injective
  rw [diagramFamilyTranspose, uncurry_natural_left, uncurry_curry,
    diagramFamilyTranspose, uncurry_curry, uncurry_pre_app]
  rfl

lemma diagramFamilyTranspose_vertex {A K X : SSet.{u}} (f : A ⟶ (ihom K).obj X)
    (k : K _⦋0⦌) :
    (diagramFamilyTranspose f).app (Opposite.op ⦋0⦌) k =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt k) := by
  let v : 𝟙_ SSet.{u} ⟶ K := (SSet.unitHomEquiv K).symm k
  have hv : SSet.unitHomEquiv K v = k := (SSet.unitHomEquiv K).apply_symm_apply k
  have he : f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt k =
      CartesianMonoidalCategory.lift (SSet.const k) (𝟙 A) ≫ uncurry f := by
    simpa only [curry_uncurry] using _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.curry_evaluateFunctorAt_vertex (uncurry f) k
  have hl : SSet.unitHomEquiv _ (v ≫ diagramFamilyTranspose f) =
      (diagramFamilyTranspose f).app (Opposite.op ⦋0⦌) k := by
    change (diagramFamilyTranspose f).app (Opposite.op ⦋0⦌)
      (v.app (Opposite.op ⦋0⦌) PUnit.unit) = _
    change (diagramFamilyTranspose f).app (Opposite.op ⦋0⦌) (SSet.unitHomEquiv K v) = _
    rw [hv]
  rw [← hl]
  apply congrArg (SSet.unitHomEquiv _)
  apply uncurry_injective
  rw [uncurry_natural_left, diagramFamilyTranspose, uncurry_curry,
    curry', uncurry_curry, he, ← Category.assoc, ← Category.assoc]
  apply congrArg (fun t => t ≫ uncurry f)
  rfl

end SerrePositivity.KST.LocalizingInvariants
