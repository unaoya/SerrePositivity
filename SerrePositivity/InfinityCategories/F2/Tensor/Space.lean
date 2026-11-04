module

public import SerrePositivity.InfinityCategories.F2.Presentable.NativeAdjointFunctorCriterion
public import SerrePositivity.InfinityCategories.F2.Presentable.SpacePresentable
public import SerrePositivity.InfinityCategories.HomotopyLimits.PostcompositionAdjunction

/-!
概要：小さい空間を固定した対象とのテンソルへ送る関手。
方針：写像空間 Map(M,−) を同じ宇宙の空間値関手に表示し、その左随伴を取る。
使われ方：集合値前層と E 値前層の間の写像空間を比較する。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
open F2.Presentable

variable {E : SSet.{u + 1}} [Quasicategory E]

/-- 同じ小さい Hom 模型をテンソル関手の随伴と比較式の両方に使う。 -/
structure SpaceTensorData (M : E _⦋0⦌) where
  hom : E ⟶ SpaceInfinity.{u}
  represents : FunctorIso (covariantRepresentableInfinity M)
    ((SSet.uliftFunctor.{u + 2, u + 1}).map hom ≫ F2.Compact.spaceUniverseDiagram)
  tensor : SpaceInfinity.{u} ⟶ E
  adjunction : QCatAdjunction tensor hom

def spaceTensorData (hE : F2.Presentable.IsPresentable E) (M : E _⦋0⦌) : SpaceTensorData M := by
  classical
  let spec := hE.isAccessible.exists_smallCovariantHom M
  let H := spec.choose
  let cert := Classical.choice spec.choose_spec
  have hHa : IsAccessibleFunctor H := by
    simpa only [Category.id_comp] using
      smallHomComposite_isAccessible_native hE.isAccessible (𝟙 E)
        (isAccessibleFunctor_id E) M H cert
  have hHl : PreservesSmallLimits H := by
    simpa only [Category.id_comp] using smallHomComposite_preservesSmallLimits_native
      (𝟙 E) (adjunction_preservesSmallLimits (QCatAdjunction.refl E)) M H cert
  let adj := (exists_leftAdjoint_iff_accessible_preservesLimits space_isPresentable hE H).mpr
    ⟨hHa, hHl⟩
  exact ⟨H, cert, adj.choose, Classical.choice adj.choose_spec⟩

/-- X ↦ X ⊗ M。全単体で定まる ∞ 関手。 -/
def tensorSpaceFunctor (hE : F2.Presentable.IsPresentable E) (M : E _⦋0⦌) :
    SpaceInfinity.{u} ⟶ E :=
  (spaceTensorData hE M).tensor

/-- テンソルと Hom の随伴を図式圏に移した写像空間の比較。 -/
def tensorSpaceFunctor_diagramHom (hE : F2.Presentable.IsPresentable E) (M : E _⦋0⦌)
    {K : SSet.{u + 1}} (X : K ⟶ SpaceInfinity.{u}) (F : K ⟶ E) :
    QCatEquivalence (pinchedHom (functorVertex (X ≫ tensorSpaceFunctor hE M)) (functorVertex F))
      (pinchedHom (functorVertex X) (functorVertex (F ≫ (spaceTensorData hE M).hom))) :=
  QCatAdjunction.pinchedHomEquivalence
    (HomotopyLimits.postcompositionAdjunction (spaceTensorData hE M).adjunction K)
    (functorVertex X) (functorVertex F)

end SerrePositivity.InfinityCategories
