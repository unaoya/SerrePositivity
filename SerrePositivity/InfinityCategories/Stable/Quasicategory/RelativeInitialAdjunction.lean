module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import Mathlib.AlgebraicTopology.Quasicategory.Basic
public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.HomotopyCat
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Opposite
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Iso
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Types.Basic
public import Mathlib.CategoryTheory.NatTrans
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import SerrePositivity.InfinityCategories.Core.Equivalence
public import SerrePositivity.InfinityCategories.Core.EquivalenceCalculus
public import SerrePositivity.InfinityCategories.Core.FullyFaithful
public import SerrePositivity.InfinityCategories.Core.FunctorHomotopy
public import SerrePositivity.InfinityCategories.Core.KanHomotopyEquivalence
public import SerrePositivity.InfinityCategories.Core.MappingSpaceMap
public import SerrePositivity.InfinityCategories.Core.MappingSpaceRightKan
public import SerrePositivity.InfinityCategories.Core.RelativeInitialBoundary
public import SerrePositivity.InfinityCategories.Core.SimplicialHomotopyEquivalence
public import SerrePositivity.InfinityCategories.F1B.Cofinality.InitialBoundaryMappingSpace
public import SerrePositivity.InfinityCategories.F1B.FunctorCategories.FunctorHomCorrespondence
public import SerrePositivity.InfinityCategories.PinchedHom.Basic

/-!
分割で生成：docstring を書き直すこと
概要：相対始点境界を充填する切断は、元の射影の左随伴になる。
方針：相対充填で得る元の写像空間の同値に、可逆な指定単位で前合成する。
規約：随伴や写像空間の同値性を追加仮定にしない。使われ方：K-8 の D 包含。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.InfinityCategories.Stable.Quasicategory
open SerrePositivity.KST.LocalizingInvariants

variable {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
  {F : X ⟶ Y} {G : Y ⟶ X}

/-- 切断の厳密な恒等から得る可逆な単位候補。 -/
def sectionUnit (h : F ≫ G = 𝟙 X) : FunctorHom (𝟙 X) (F ≫ G) :=
  eqToHom (congrArg (fun f => SSet.HomotopyCategory.mk (functorVertex f)) h.symm)

instance sectionUnit_isIso (h : F ≫ G = 𝟙 X) : IsIso (_root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.sectionUnit h) :=
  inferInstanceAs (IsIso (eqToHom _))

/-- 相対始点境界を充填する厳密切断は、全写像空間の意味で充満忠実。 -/
lemma fullyFaithful_of_relativeInitialSection (h : F ≫ G = 𝟙 X)
    (hF : ∀ x, InitialBoundaryLifting G (F.app (Opposite.op ⦋0⦌) x)) :
    IsFullyFaithful F := by
  have hfg : IsFullyFaithful (F ≫ G) := h.symm ▸ isFullyFaithful_id X
  intro x y
  have hg := SerrePositivity.InfinityCategories.F1B.pinchedHomMap_equivalence_of_initialBoundary G _
    (F.app (Opposite.op ⦋0⦌) y) (hF x)
  have hc := (hfg x y).isQCatEquivalence
  rw [pinchedHomMap_comp] at hc
  exact (hg.isQCatEquivalence.cancel_right hc).isSimplicialHomotopyEquivalence

end SerrePositivity.InfinityCategories.Stable.Quasicategory

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.fullyFaithful_of_relativeInitialSection := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.fullyFaithful_of_relativeInitialSection

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.sectionUnit (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.sectionUnit := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.sectionUnit

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.sectionUnit_isIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.sectionUnit_isIso := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.sectionUnit_isIso

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.sectionUnit._proof_1 := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.sectionUnit._proof_1
