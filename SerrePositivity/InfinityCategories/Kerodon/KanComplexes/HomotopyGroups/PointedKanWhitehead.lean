module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy
public import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
public import Mathlib.AlgebraicTopology.SimplicialSet.RelativeMorphism
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Opposite
public import Mathlib.Basic.UnivLE
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.Comma.Basic
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Discrete.Basic
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Over
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.WalkingPair
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Cospan
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Types.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Basic
public import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty
public import Mathlib.CategoryTheory.NatTrans
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.PUnit
public import Mathlib.CategoryTheory.Subfunctor.Basic
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import SerrePositivity.HomotopicalAlgebra.Simplicial.MonoRightLiftingRelativeHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.F1PointedAcyclicFibrationLifting
public import SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.PullbackKanSequence
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.HomotopyIsomorphism
public import SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.FreePathSpace
public import SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.MappingPathSpace
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.MonoRightHomotopyEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping
public import SerrePositivity.Spectra.PointedSimplicialSet.Basic

/-!
概要：点つき Kan 複体間の全基点 π_* 同型は実際の基点固定ホモトピー逆を持つ。
方針：mapping path の二つの端点で同型性を打ち消し、相対 Whitehead の充填で切断を作る。
規約：逆射と両方向の区間ホモトピーを構成する。HT-KQ は使わない。
使われ方：Goerss–Jardine I §§7–8、Kerodon §3.2.6（Tag 00WL）、BF 1978 §2。有理化の乗法射の実現。

対応節は Kerodon 3.2（Tag 00V2）。
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.SimplicialModel
open scoped _root_.Simplicial

namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：π_* 同型の点つき Kan 射の mapping path の終点射も全基点 π_* 同型。
方針：源への射影と元の射の合成を path の始点で比較し、終点へ移す。
規約：零次数を含む全基点での主張。
使われ方：Goerss–Jardine I §§7–8。Whitehead の fibration 置換。 -/
theorem mappingPathProjection_piIsomorphism {X Y : PointedSimplicialSet.{u}}
    [KanComplex X.right] [KanComplex Y.right] (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism f.right) : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathProjection f).right := by
  have hr : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathRetraction f).right :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.kanPiIsomorphism_of_monoRight _ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathRetraction_rlp f)
  have hsq : (pullback.fst (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint Y 1) f).right ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint Y 1).right =
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathRetraction f).right ≫ f.right :=
    congrArg Under.Hom.right (pullback.condition (f := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint Y 1) (g := f))
  have hfst : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (pullback.fst (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint Y 1) f).right := by
    apply _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism.of_comp (g := (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint Y 1).right) _
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.kanPiIsomorphism_of_monoRight _ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint_rlp Y 1))
    rw [hsq]
    exact hr.comp hf
  exact hfst.comp (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.kanPiIsomorphism_of_monoRight _ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint_rlp Y 0))

/-- 概要：上の mapping path の終点射は全ての単射への RLP を持つ。
方針：相対 Whitehead の充填へ mapping path の基点を渡す。
規約：源の非空性は点つき対象の基点で供給する。
使われ方：Goerss–Jardine I §§7–8、BF 1978 §2。逆射のための切断。 -/
theorem mappingPathProjection_rlp_of_piIsomorphism {X Y : PointedSimplicialSet.{u}}
    [KanComplex X.right] [KanComplex Y.right] (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism f.right) :
    (MorphismProperty.monomorphisms SSet.{u}).rlp (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathProjection f).right :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fibration_rlp_of_piIsomorphism _ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mappingPathProjection_piIsomorphism f hf)
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPath f).basepoint

/-- 概要：全単射 RLP の射で等しい二つの点つき射は基点固定でホモトピック。
方針：源の基点包含を固定する垂直ホモトピーを相対充填する。
規約：源・標的の Kan 性は不要。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.1（Tag 00V4）。Whitehead の逆射の両方向の比較。 -/
theorem exists_pointedHomotopy_of_comp_eq {A E B : PointedSimplicialSet.{u}}
    (p : E ⟶ B) (hp : (MorphismProperty.monomorphisms SSet.{u}).rlp p.right)
    (a b : A ⟶ E) (hab : a ≫ p = b ≫ p) :
    ∃ H : SSet.Homotopy a.right b.right,
      A.hom ▷ (Δ[1] : SSet.{u}) ≫ H.h =
        toUnit (𝟙_ SSet.{u} ⊗ (Δ[1] : SSet.{u})) ≫ E.hom := by
  let : Mono A.hom := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basepoint_mono A
  have hbase : A.hom ≫ a.right = A.hom ≫ b.right := by rw [Under.w a, Under.w b]
  obtain ⟨H, _hHp, hH⟩ := MonoRightLiftingRelativeHomotopy.exists_relative_vertical_homotopy
    p.right hp A.hom a.right b.right (congrArg Under.Hom.right hab) hbase
  refine ⟨H, ?_⟩
  rw [hH, Under.w a]
  rfl

/-- 概要：点つき Kan 複体間の全基点 π_* 同型は基点を固定するホモトピー逆を持つ。
方針：mapping path の二つの RLP 射の間で切断を選び、合成の等式を相対ホモトピーへ戻す。
規約：両方向とも恒等射から合成への実際の区間ホモトピーを返す。
使われ方：Goerss–Jardine I §§7–8、Kerodon §3.2.6（Tag 00WL）、BF 1978 §2。一般の Kan Whitehead。 -/
theorem exists_pointedHomotopyInverse {X Y : PointedSimplicialSet.{u}}
    [KanComplex X.right] [KanComplex Y.right] (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism f.right) :
    ∃ g : Y ⟶ X,
      (∃ H : SSet.Homotopy (𝟙 X.right) (f ≫ g).right,
        X.hom ▷ (Δ[1] : SSet.{u}) ≫ H.h =
          toUnit (𝟙_ SSet.{u} ⊗ (Δ[1] : SSet.{u})) ≫ X.hom) ∧
      (∃ H : SSet.Homotopy (𝟙 Y.right) (g ≫ f).right,
        Y.hom ▷ (Δ[1] : SSet.{u}) ≫ H.h =
          toUnit (𝟙_ SSet.{u} ⊗ (Δ[1] : SSet.{u})) ≫ Y.hom) := by
  let p := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathProjection f
  let r := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathRetraction f
  let u := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathUnit f
  have hp := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mappingPathProjection_rlp_of_piIsomorphism f hf
  have hr := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathRetraction_rlp f
  obtain ⟨s, hs⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.exists_pointedSection p hp
  let g := s ≫ r
  have hup : u ≫ p = f := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathUnit_projection f
  have hur : u ≫ r = 𝟙 X := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathUnit_retraction f
  have hX : u ≫ p = (f ≫ s) ≫ p := by rw [Category.assoc, hs, Category.comp_id, hup]
  have hY : s ≫ r = (g ≫ u) ≫ r := by rw [Category.assoc, hur, Category.comp_id]
  obtain ⟨HX, hHX⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.exists_pointedHomotopy_of_comp_eq p hp u (f ≫ s) hX
  obtain ⟨HY, hHY⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.exists_pointedHomotopy_of_comp_eq r hr s (g ≫ u) hY
  refine ⟨g, ?_, ?_⟩
  · let H : SSet.Homotopy (𝟙 X.right) (f ≫ g).right := {
      h := HX.h ≫ r.right
      h₀ := by rw [← Category.assoc, HX.h₀]; exact congrArg Under.Hom.right hur
      h₁ := by rw [← Category.assoc, HX.h₁]; rfl
      rel := by ext m ⟨⟨z, hz⟩, t⟩; exact hz.elim }
    refine ⟨H, ?_⟩
    change X.hom ▷ (Δ[1] : SSet.{u}) ≫ (HX.h ≫ r.right) = _
    rw [← Category.assoc, hHX, Category.assoc, Under.w r]
  · let H : SSet.Homotopy (𝟙 Y.right) (g ≫ f).right := {
      h := HY.h ≫ p.right
      h₀ := by rw [← Category.assoc, HY.h₀]; exact congrArg Under.Hom.right hs
      h₁ := by
        rw [← Category.assoc, HY.h₁]
        exact congrArg Under.Hom.right (Category.assoc g u p |>.trans (congrArg (g ≫ ·) hup))
      rel := by ext m ⟨⟨z, hz⟩, t⟩; exact hz.elim }
    refine ⟨H, ?_⟩
    change Y.hom ▷ (Δ[1] : SSet.{u}) ≫ (HY.h ≫ p.right) = _
    rw [← Category.assoc, hHY, Category.assoc, Under.w p]

end

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
