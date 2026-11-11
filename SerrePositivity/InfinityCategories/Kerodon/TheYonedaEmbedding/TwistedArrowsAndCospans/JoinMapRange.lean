module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.JoinCells
public import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexOp

/-!
概要：join の両因子の射の像を左右の像の条件に分解する。
方針：切断位置を固定し、左右の補った単体の前像を独立に取る。
規約：射に単射性は要求しない。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、edgewise の境界面の像とその共通部分の接合。

対応節は Kerodon 8.1（Tag 03JB）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans

/-- 概要：補った次数で射の像に属することは補った単体の前像の存在と同値。
方針：空区間では唯一の空単体を使い、正次数では射の成分の像の定義を使う。
規約：空区間も含む。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、join の射の像の左右の分解。 -/
lemma Join.augMem_range_iff {X Y : SSet.{u}} (f : X ⟶ Y) (r : ℕ) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj Y r) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.Join.augMem (Subcomplex.range f) r a ↔ ∃ b : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj X r, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom f r b = a := by
  cases r with
  | zero =>
    constructor
    · intro _
      exact ⟨PUnit.unit, @Subsingleton.elim PUnit inferInstance _ _⟩
    · intro _
      trivial
  | succ r => rfl

/-- 概要：join の射の像は左の像と右の像の条件の共通部分。
方針：像の単体の切断を一致させ、左右の前像を同じ切断の一単体に組み直す。
規約：左右とも一般の射に対して成立する。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、edgewise の各境界面の像の計算。 -/
lemma joinMap_range {X X' Y Y' : SSet.{u}} (f : X ⟶ X') (g : Y ⟶ Y') :
    Subcomplex.range (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f g) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinSubcomplexLeft (Subcomplex.range f) Y' ⊓ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinSubcomplexRight X' (Subcomplex.range g) := by
  ext n s
  change (∃ t, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f g).app n t = s) ↔
    s ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinSubcomplexLeft (Subcomplex.range f) Y').obj n ∧
      s ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinSubcomplexRight X' (Subcomplex.range g)).obj n
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.Join.mem_joinSubcomplexLeft, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.Join.mem_joinSubcomplexRight]
  rcases s with ⟨c, x, y⟩
  rw [Join.augMem_range_iff, Join.augMem_range_iff]
  constructor
  · rintro ⟨⟨c', x', y'⟩, h⟩
    have hc : c' = c := congrArg Sigma.fst h
    subst c'
    have hp := eq_of_heq (Sigma.mk.inj h).2
    exact ⟨⟨x', congrArg Prod.fst hp⟩, ⟨y', congrArg Prod.snd hp⟩⟩
  · rintro ⟨⟨x', hx⟩, ⟨y', hy⟩⟩
    refine ⟨⟨c, x', y'⟩, ?_⟩
    exact congrArg (Sigma.mk c) (Prod.ext hx hy)

/-- 概要：単体集合の射の反転の像は元の像の反転。
方針：各次数の反転の単体の同値で前像を移す。
規約：射 f の単射性は不要。
使われ方：Kerodon Remark 8.1.1.2（Tag 03JH）、edgewise の面の左因子の像の計算。 -/
lemma subcomplex_range_opFunctor_map {X Y : SSet.{u}} (f : X ⟶ Y) :
    Subcomplex.range (SSet.opFunctor.map f) = (Subcomplex.range f).op := by
  ext n s
  change (∃ t, (SSet.opFunctor.map f).app n t = s) ↔
    ∃ t, f.app n t = SSet.opObjEquiv s
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨SSet.opObjEquiv t, ?_⟩
    have h := congrArg SSet.opObjEquiv ht
    simpa only [SSet.opFunctor_map, Equiv.apply_symm_apply] using h
  · rintro ⟨t, ht⟩
    refine ⟨SSet.opObjEquiv.symm t, ?_⟩
    apply SSet.opObjEquiv.injective
    simpa only [SSet.opFunctor_map, Equiv.apply_symm_apply] using ht

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
