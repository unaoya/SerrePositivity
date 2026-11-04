module
public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.Basic.Opposite
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Enriched.Basic
public import Mathlib.CategoryTheory.Enriched.Ordinary.Basic
public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Iso
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Types.Basic
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import SerrePositivity.InfinityCategories.Core.RightFibration
public import SerrePositivity.InfinityCategories.F1.Categories.CatInfinity
public import SerrePositivity.InfinityCategories.F1.Diagrams.RelativeSectionDiagram
public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftFibrationInfinity
public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftFibrationMappingSpaces
public import SerrePositivity.InfinityCategories.F1.KanModels.KanEnrichedDiagram
public import SerrePositivity.InfinityCategories.F1.Transport.SimplexDomains
public import SerrePositivity.InfinityCategories.F1.Transport.SimplexFirstVertexNaturality
public import SerrePositivity.InfinityCategories.F1B.IsoEndpointNormalization
public import SerrePositivity.InfinityCategories.Stable.Straightening.StraighteningBaseChangeLeftEndpoints

/-!
分割で生成：docstring を書き直すこと
 # 像の単体へ輸送した同じ切断点を、元の底側の scaffold 復元像へ接続する
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration

private lemma point_normalize_both_inv {C : Type*} [Category C] {a b a' b' z t : C}
    (e : a ≅ b) (hs : a = a') (ht : b = b') (v : z ⟶ b) (w : z ⟶ b')
    (f : a' ⟶ t) (hp : v ≫ (eqToIso ht).hom = w) :
    v ≫ e.inv ≫ (eqToIso hs).hom ≫ f =
      w ≫ (F2.isoNormalizeEndpoints e hs ht).inv ≫ f := by
  rw [← hp]
  simp only [F2.isoNormalizeEndpoints, Iso.trans_inv, Iso.symm_inv,
    Category.assoc, Iso.hom_inv_id_assoc]

variable {E B D : SSet.{u}} (p : E ⟶ B) [LeftFibration p] [Quasicategory B]
  (k : D ⟶ B)

/-- 同じ相対切断の点を、像の単体での切断 Kan 対象へ等式で輸送する。 -/
def straighteningBaseChangeImageSectionPoint (c : TransportSimplexCategory D)
    (v : (((relativeSectionEnrichedDiagram
      (transportSimplexDomainFunctor D ⋙ Over.map k)).obj c).obj
        (leftFibrationObjectOf p)).obj _⦋0⦌) :=
  Eq.mp (congrArg (fun T : KanObject.{u} => T.obj _⦋0⦌)
    (straighteningBaseChangeLeft_section_eq k (leftFibrationObjectOf p) c)) v

end SerrePositivity.KST.Fibration
