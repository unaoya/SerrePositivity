module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.FilteredSpaceBridgeInput
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.UniverseBoundary
/-!
概要：境界が指定基点に定数である球面単体を、宇宙持ち上げと厳密に比較する。
方針：標準単体・境界の同型と、ULift 関手の完全忠実性を使う。
規約：指定基点と元の境界条件を保持する。
使われ方：持ち上げた native 値の π を元の native 値へ戻す基礎データ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
open CategoryTheory SSet
open _root_.SerrePositivity.KST.Spectra
open scoped _root_.Simplicial
variable {X Y : SSet.{u}} {n : ℕ} {x : X _⦋0⦌}

lemma dgBarCompactUliftConst {A : SSet.{u}} (x : X _⦋0⦌) :
    (SSet.uliftFunctor.{v, u}).map (SSet.const x : A ⟶ X) = SSet.const (ULift.up x) := by
  ext d s
  rfl

/-- 同じ球面単体と基点を、標準境界の宇宙同型で上げる。 -/
def dgBarCompactPointedSimplexUp (f : X.PtSimplex n x) :
    ((SSet.uliftFunctor.{v, u}).obj X).PtSimplex n (ULift.up x) where
  map := (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso.{u, v} n).inv ≫ (SSet.uliftFunctor.{v, u}).map f.map
  comm := by
    simp only [Subcomplex.ofSimplex_ι, SSet.comp_const]
    apply (cancel_epi (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftBoundaryIso.{u, v} n).hom).mp
    simp only [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftBoundaryIso_ι]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    have hf : (boundary n).ι ≫ f.map = SSet.const x := by
      simpa only [Subcomplex.ofSimplex_ι, SSet.comp_const] using f.comm
    rw [← Functor.map_comp, hf, dgBarCompactUliftConst, SSet.comp_const]

/-- 同じ持ち上げた球面単体を、元の小さい宇宙へ戻す。 -/
def dgBarCompactPointedSimplexDown
    (f : ((SSet.uliftFunctor.{v, u}).obj X).PtSimplex n (ULift.up x)) : X.PtSimplex n x where
  map := (SSet.uliftFunctor.{v, u}).preimage ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso.{u, v} n).hom ≫ f.map)
  comm := by
    simp only [Subcomplex.ofSimplex_ι, SSet.comp_const]
    apply (SSet.uliftFunctor.{v, u}).map_injective
    rw [Functor.map_comp, Functor.map_preimage, ← Category.assoc,
      ← _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftBoundaryIso_ι, Category.assoc]
    have hf : (boundary n).ι ≫ f.map = SSet.const (ULift.up x) := by
      simpa only [Subcomplex.ofSimplex_ι, SSet.comp_const] using f.comm
    rw [hf, SSet.comp_const, dgBarCompactUliftConst]

/-- 指定基点での境界定数単体の、元を保つ全単射。 -/
def dgBarCompactUliftPointedSimplexEquiv (X : SSet.{u}) (n : ℕ) (x : X _⦋0⦌) :
    X.PtSimplex n x ≃ ((SSet.uliftFunctor.{v, u}).obj X).PtSimplex n (ULift.up x) where
  toFun := dgBarCompactPointedSimplexUp
  invFun := dgBarCompactPointedSimplexDown
  left_inv f := by
    apply RelativeMorphism.ext
    apply (SSet.uliftFunctor.{v, u}).map_injective
    change (SSet.uliftFunctor.{v, u}).map ((SSet.uliftFunctor.{v, u}).preimage
      ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso.{u, v} n).hom ≫
        ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso.{u, v} n).inv ≫ (SSet.uliftFunctor.{v, u}).map f.map))) =
      (SSet.uliftFunctor.{v, u}).map f.map
    rw [Functor.map_preimage, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  right_inv f := by
    apply RelativeMorphism.ext
    change (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso.{u, v} n).inv ≫
      (SSet.uliftFunctor.{v, u}).map ((SSet.uliftFunctor.{v, u}).preimage
        ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso.{u, v} n).hom ≫ f.map)) = f.map
    rw [Functor.map_preimage, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
