module
public import SerrePositivity.KST.SConstruction.FundamentalGroupoidGenerators
public import SerrePositivity.KST.SConstruction.FundamentalLoopHom

/-! # 既存の Kan 基本群の置換前の辺と二単体による表示
概要：anodyne 射の後の実際の基本群を、元の辺と二単体の基本亜群の基点の自己射で表示する。
方針：基本群とホモトピー圏の loop 射の同値を、基本亜群比較の充満忠実性と合成する。
規約：元の頂点を基点とし、辺の向きを保つ。使われ方：π₀ K 比較の生成・関係の証明。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open Spectra
open scoped Simplicial

/-- 元の loop 辺の後合成は、元の境界定数一次単体の後合成と一致する。 -/
lemma fundamentalLoopEdge_mapSimplex {A B : SSet.{u}} (i : A ⟶ B) {x : A _⦋0⦌}
    (s : A.PtSimplex 1 x) :
    fundamentalLoopEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex i rfl s) =
      (fundamentalLoopEdge s).map ((truncation 2).map i) := by
  apply SSet.Truncated.Edge.ext
  exact SSet.yonedaEquiv_comp s.map i

/-- Kan 値 anodyne 射の後の実際の基本群を、元の辺と二単体の基本亜群で表示する。 -/
def kanAnodyneLoopPresentation {A B : SSet.{u}} [KanComplex B] (i : A ⟶ B)
    (hi : anodyneExtensions i) (x : A _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup B 0 (i.app _ x) ≃
      (FreeGroupoid.mk (SSet.HomotopyCategory.mk (X := A) x) ⟶
        FreeGroupoid.mk (SSet.HomotopyCategory.mk x)) :=
  (fundamentalLoopHomEquiv B (i.app _ x)).trans
    ((fundamentalGroupoidComparison_fullyFaithful i hi).homEquiv
      (X := FreeGroupoid.mk (SSet.HomotopyCategory.mk x))
      (Y := FreeGroupoid.mk (SSet.HomotopyCategory.mk x))).symm

/-- 表示を元の比較関手で写すと、同じ基本群のホモトピー圏の loop 射を回収する。 -/
lemma kanAnodyneLoopPresentation_apply {A B : SSet.{u}} [KanComplex B] (i : A ⟶ B)
    (hi : anodyneExtensions i) (x : A _⦋0⦌) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup B 0 (i.app _ x)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fundamentalGroupoidComparison i).map (kanAnodyneLoopPresentation i hi x a) =
      fundamentalLoopHomEquiv B (i.app _ x) a :=
  (fundamentalGroupoidComparison_fullyFaithful i hi).homEquiv.apply_symm_apply _

/-- 表示の逆をホモトピー圏へ戻すと、元の形式的な道の像を回収する。 -/
lemma kanAnodyneLoopPresentation_symm_apply {A B : SSet.{u}} [KanComplex B] (i : A ⟶ B)
    (hi : anodyneExtensions i) (x : A _⦋0⦌)
    (a : FreeGroupoid.mk (SSet.HomotopyCategory.mk (X := A) x) ⟶
      FreeGroupoid.mk (SSet.HomotopyCategory.mk x)) :
    fundamentalLoopHomEquiv B (i.app _ x) ((kanAnodyneLoopPresentation i hi x).symm a) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fundamentalGroupoidComparison i).map a :=
  (fundamentalLoopHomEquiv B (i.app _ x)).apply_symm_apply _

/-- 元の境界定数単体の類は、同じ元の loop 辺の形式的な類に対応する。 -/
lemma kanAnodyneLoopPresentation_mk {A B : SSet.{u}} [KanComplex B] (i : A ⟶ B)
    (hi : anodyneExtensions i) (x : A _⦋0⦌) (s : A.PtSimplex 1 x) :
    kanAnodyneLoopPresentation i hi x (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex i rfl s)) =
      FreeGroupoid.homMk (SSet.Truncated.HomotopyCategory.homMk (fundamentalLoopEdge s)) := by
  apply fundamentalGroupoidComparison_map_injective i hi _ _
  rw [kanAnodyneLoopPresentation_apply, fundamentalLoopHomEquiv_mk,
    fundamentalLoopEdge_mapSimplex]
  have he := CategoryTheory.Functor.congr_hom (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fundamentalGroupoidComparison_fac i)
    (SSet.Truncated.HomotopyCategory.homMk (fundamentalLoopEdge s))
  exact he.symm

/-- 基本群の単位は元の基本亜群の恒等射で表示される。 -/
lemma kanAnodyneLoopPresentation_one {A B : SSet.{u}} [KanComplex B] (i : A ⟶ B)
    (hi : anodyneExtensions i) (x : A _⦋0⦌) :
    kanAnodyneLoopPresentation i hi x 1 = 𝟙 _ := by
  apply fundamentalGroupoidComparison_map_injective i hi _ _
  rw [kanAnodyneLoopPresentation_apply, fundamentalLoopHomEquiv_one,
    CategoryTheory.Functor.map_id]
  rfl

/-- 基本群の積は元の形式的な道を辿る順の合成で表示される。 -/
lemma kanAnodyneLoopPresentation_mul {A B : SSet.{u}} [KanComplex B] (i : A ⟶ B)
    (hi : anodyneExtensions i) (x : A _⦋0⦌) (a b : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup B 0 (i.app _ x)) :
    kanAnodyneLoopPresentation i hi x (a * b) =
      kanAnodyneLoopPresentation i hi x a ≫ kanAnodyneLoopPresentation i hi x b := by
  apply fundamentalGroupoidComparison_map_injective i hi _ _
  rw [CategoryTheory.Functor.map_comp, kanAnodyneLoopPresentation_apply,
    kanAnodyneLoopPresentation_apply, kanAnodyneLoopPresentation_apply]
  exact fundamentalLoopHomEquiv_mul B (i.app _ x) a b

/-- 基本群の逆元は元の形式的な道の逆で表示される。 -/
lemma kanAnodyneLoopPresentation_inv {A B : SSet.{u}} [KanComplex B] (i : A ⟶ B)
    (hi : anodyneExtensions i) (x : A _⦋0⦌) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup B 0 (i.app _ x)) :
    kanAnodyneLoopPresentation i hi x a⁻¹ = inv (kanAnodyneLoopPresentation i hi x a) := by
  apply (cancel_epi (kanAnodyneLoopPresentation i hi x a)).mp
  rw [← kanAnodyneLoopPresentation_mul, mul_inv_cancel, kanAnodyneLoopPresentation_one,
    IsIso.hom_inv_id]

end SerrePositivity.KST.SConstruction
