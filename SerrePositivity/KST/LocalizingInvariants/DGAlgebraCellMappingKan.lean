module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraCellMappingHorn
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.UniverseHorns
public import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex

/-!
概要：native cell 源の実乗法的写像単体集合は Kan 複体。
方針：実 AW ホーン充填を D のホーン・標準単体の宇宙同型で移す。
規約：任意の可換係数環と標的代数。モデル構造を入力しない。
使われ方：Postnikov 拡大の導来写像空間比較の実 Kan 模型。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory Opposite
open scoped Simplicial
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories

namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (A B : Mon (Complex R))

lemma multiplicativeCellMapping_horn_extension (n : ℕ) (i : Fin (n + 2))
    (a : (SSet.horn (n + 1) i : SSet.{u}) ⟶
      multiplicativeMappingSimplices R (cellResolution R A) B) :
    ∃ b : (Δ[n + 1] : SSet.{u}) ⟶ multiplicativeMappingSimplices R (cellResolution R A) B,
      (SSet.horn (n + 1) i).ι ≫ b = a := by
  obtain ⟨b, hb⟩ := multiplicativeCellMapping_smallHorn_extension R A B n i
    ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftHornIso.{0, u} (n + 1) i).hom ≫ a)
  refine ⟨(_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso.{0, u} (n + 1)).inv ≫ b, ?_⟩
  apply (cancel_epi (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftHornIso.{0, u} (n + 1) i).hom).mp
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftHornIso_ι, Category.assoc,
    Iso.hom_inv_id_assoc, hb]

instance multiplicativeCellMapping_kanComplex :
    SSet.KanComplex (multiplicativeMappingSimplices R (cellResolution R A) B) := by
  rw [SSet.KanComplex.iff]
  intro n i fs hf
  obtain ⟨b, hb⟩ := multiplicativeCellMapping_horn_extension R A B n i hf.desc
  refine ⟨b, fun j hj => ?_⟩
  rw [← SSet.horn.ι_ι_assoc i j hj, hb]
  exact hf.ι_desc j hj

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
