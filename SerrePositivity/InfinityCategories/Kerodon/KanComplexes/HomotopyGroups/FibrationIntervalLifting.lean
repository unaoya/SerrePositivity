module


public import Mathlib.AlgebraicTopology.ModelCategory.CategoryWithCofibrations
public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
public import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
public import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex
public import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex.MulStruct
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
public import Mathlib.AlgebraicTopology.SimplicialSet.RelativeMorphism
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Opposite
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.CommSq
public import Mathlib.CategoryTheory.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.LiftingProperties.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Types.Basic
public import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty
public import Mathlib.CategoryTheory.NatTrans
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Subfunctor.Basic
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Function.Basic
public import SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneIntervalEndpoints
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.HomotopyGroups
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.HomotopyIndexing
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.HomotopyIsomorphism
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromTopologicalSpacesToSimplicialSets.HomotopyZeroRelations

/-!
概要：Kan fibration に沿う区間の持ち上げと π₀ 全射からの頂点の持ち上げ。
方針：区間の端点包含の anodyne 性を使い、零次数の等式を単一の RelStruct へ戻す。
規約：全空間の参照頂点を指定する。HT-KQ を使わない。
使われ方：Goerss–Jardine I §§7–8、Kerodon §3.2.6（Tag 00WL）。acyclic Kan fibration の全境界 RLP。

対応節は Kerodon 3.2（Tag 00V2）。
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open SerrePositivity.SimplicialModel
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra
end SerrePositivity.KST.Spectra
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups
open _root_.SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：Kan fibration の底の区間は指定した始点から持ち上がる。
方針：パラメータ単体集合の始点包含の anodyne 性へ RLP を適用する。
規約：パラメータ A に Kan 性や有限性を仮定しない。
使われ方：Goerss–Jardine I §7、Kerodon §3.1.3（Tag 00TJ）。境界上の持ち上げを fiber へ移す。 -/
theorem exists_fibration_interval_lift {A E B : SSet.{u}}
    (p : E ⟶ B) [Fibration p] (a : A ⟶ E)
    (q : A ⊗ (Δ[1] : SSet.{u}) ⟶ B) (ha : a ≫ p = SSet.ι₀ ≫ q) :
    ∃ l : A ⊗ (Δ[1] : SSet.{u}) ⟶ E, SSet.ι₀ ≫ l = a ∧ l ≫ p = q := by
  have hp : J.rlp p := (fibration_iff _).1 inferInstance
  let : HasLiftingProperty (SSet.ι₀ (X := A)) p :=
    AnodyneHomotopy.endpoint_zero_anodyne A p hp
  let sq : CommSq a SSet.ι₀ p q := ⟨ha⟩
  exact ⟨sq.lift, sq.fac_left, sq.fac_right⟩

/-- 概要：参照頂点の零次数で全射となる Kan fibration は頂点でも全射。
方針：底の頂点の類の逆像を一つの単体で表し、RelStruct の辺を端点から持ち上げる。
規約：非空性は全空間の参照頂点 e₀ として明示する。
使われ方：Goerss–Jardine I §§7–8、Kerodon §3.2.6（Tag 00WL）。零次元の境界の充填。 -/
theorem fibration_surjective_vertices_of_zero {E B : SSet.{u}} [KanComplex E] [KanComplex B]
    (p : E ⟶ B) [Fibration p] (e₀ : E _⦋0⦌)
    (hp₀ : Function.Surjective (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map 0 p (x := e₀) rfl)) :
    Function.Surjective (p.app (Opposite.op ⦋0⦌)) := by
  intro b
  let t : B.PtSimplex 0 (p.app _ e₀) := (PtSimplex.equiv₀ _).symm b
  obtain ⟨a, ha⟩ := hp₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.mk 0 t)
  obtain ⟨s, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromTopologicalSpacesToSimplicialSets.KanHomotopy.mk_surjective 0 a
  have heq : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.mk 0 t = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.mk 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex p rfl s) := ha.symm
  obtain ⟨r⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromTopologicalSpacesToSimplicialSets.KanHomotopy.mk_eq_iff_relStruct 0 t (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex p rfl s) 0).1 heq
  have hp : J.rlp p := (fibration_iff _).1 inferInstance
  let : HasLiftingProperty (stdSimplex.δ.{u} (1 : Fin 2)) p :=
    AnodyneHomotopy.delta_anodyne 1 0 (by decide) p hp
  let sq : CommSq s.map (stdSimplex.δ (1 : Fin 2)) p r.map := ⟨r.δ_succ_map.symm⟩
  let v := SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2) ≫ sq.lift)
  refine ⟨v, ?_⟩
  have h : (stdSimplex.δ (0 : Fin 2) ≫ sq.lift) ≫ p = t.map := by
    rw [Category.assoc, sq.fac_right]
    exact r.δ_castSucc_map
  have hv : p.app _ v = SSet.yonedaEquiv t.map := by
    rw [← SSet.yonedaEquiv_comp]
    exact congrArg SSet.yonedaEquiv h
  exact hv.trans ((PtSimplex.equiv₀ (p.app _ e₀)).apply_symm_apply b)

/-- 概要：π_* 同型である非空な Kan fibration の頂点は全射。
方針：参照頂点の零次数の全射性だけを上の補題へ渡す。
規約：正次数の同型性はこの結論には不要。
使われ方：Goerss–Jardine I §7。acyclic fibration の全ての fiber の非空性。 -/
theorem fibration_surjective_vertices_of_piIsomorphism {E B : SSet.{u}}
    [KanComplex E] [KanComplex B] (p : E ⟶ B) [Fibration p]
    (hp : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism p) (e₀ : E _⦋0⦌) :
    Function.Surjective (p.app (Opposite.op ⦋0⦌)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fibration_surjective_vertices_of_zero p e₀ (hp e₀ 0).surjective

end

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
