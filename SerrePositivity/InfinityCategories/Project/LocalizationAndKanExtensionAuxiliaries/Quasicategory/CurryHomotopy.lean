module


public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.HomotopyPrecomposition
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.ReflectiveLocalObjects
public import Mathlib.CategoryTheory.Comma.Arrow

/-!
概要：二変数図式の元のホモトピーを curry し、その頂点成分を元の切片と同定する。
方針：結合子で三因子を直して一回 curry し、成分の一単体を全パラメーターで照合する。
規約：端点の表示は Arrow の等号で保持。使われ方：相対三角形 prism の全 h Fun 可換式。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.CurryHomotopy
end SerrePositivity.KST.LocalizingInvariants.CurryHomotopy
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory
open _root_.SerrePositivity.KST.LocalizingInvariants.CurryHomotopy

variable {A B X : SSet.{u}} {F G : A ⊗ B ⟶ X} (H : SSet.Homotopy F G)

def homotopy : SSet.Homotopy (curry F) (curry G) where
  h := curry ((α_ A B (Δ[1] : SSet.{u})).inv ≫ H.h)
  h₀ := by
    change SSet.ι₀ ≫ curry ((α_ A B (Δ[1] : SSet.{u})).inv ≫ H.h) = curry F
    apply uncurry_injective
    rw [uncurry_natural_left, uncurry_curry, uncurry_curry]
    have he : (A ◁ (SSet.ι₀ : B ⟶ B ⊗ Δ[1])) ≫
        (α_ A B (Δ[1] : SSet.{u})).inv = SSet.ι₀ := rfl
    rw [← Category.assoc, he, H.h₀]
  h₁ := by
    change SSet.ι₁ ≫ curry ((α_ A B (Δ[1] : SSet.{u})).inv ≫ H.h) = curry G
    apply uncurry_injective
    rw [uncurry_natural_left, uncurry_curry, uncurry_curry]
    have he : (A ◁ (SSet.ι₁ : B ⟶ B ⊗ Δ[1])) ≫
        (α_ A B (Δ[1] : SSet.{u})).inv = SSet.ι₁ := rfl
    rw [← Category.assoc, he, H.h₁]
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    exact False.elim s.1.property

def sliceMap (b : B _⦋0⦌) : A ⟶ A ⊗ B := lift (𝟙 A) (SSet.const b)

def slice (b : B _⦋0⦌) := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.stableHomotopyPrecomp (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.sliceMap (A := A) b) H

def hom : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (curry F) (curry G) :=
  Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.homotopy H))

lemma component_arrow (b : B _⦋0⦌) : Arrow.mk (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.hom H) b) =
    Arrow.mk (Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.slice H b))) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.hom, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomEvaluate_homotopy]
  apply Truncated.HomotopyCategory.congr_arrowMk_homMk
  apply CategoryTheory.Functor.functorHom_ext
  intro n α
  apply ConcreteCategory.hom_ext
  intro a
  obtain ⟨⟨n⟩⟩ := n
  have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge = SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})) := by
    apply SSet.stdSimplex.ext
    intro i
    fin_cases i <;> rfl
  change H.h.app (Opposite.op ⦋n⦌)
    ((a, B.map α (Truncated.Edge.id (X := (truncation 2).obj B) b).edge),
      (Δ[1] : SSet.{u}).map α _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge) =
    H.h.app (Opposite.op ⦋n⦌) ((a, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant b n),
      (Δ[1] : SSet.{u}).map α (SSet.yonedaEquiv (𝟙 Δ[1])))
  have hb : B.map α (Truncated.Edge.id (X := (truncation 2).obj B) b).edge =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant b n :=
    (congrArg (fun v ↦ B.map α v) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one (X := B) b).symm).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant_pullback b α.unop)
  exact congrArg₂ (fun v w ↦ H.h.app (Opposite.op ⦋n⦌) ((a, v), w)) hb
    (congrArg (fun v ↦ (Δ[1] : SSet.{u}).map α v) hi)

lemma naturality [Quasicategory X] {b₀ b₁ : B _⦋0⦌} (e : B.Edge b₀ b₁) :
    (hoFunctor.map (curry F)).toFunctor.map (Truncated.HomotopyCategory.homMk e.toTruncated) ≫
      _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.hom H) b₁ = _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.hom H) b₀ ≫
        (hoFunctor.map (curry G)).toFunctor.map
          (Truncated.HomotopyCategory.homMk e.toTruncated) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.functorHomEvaluate_naturality _ _

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
