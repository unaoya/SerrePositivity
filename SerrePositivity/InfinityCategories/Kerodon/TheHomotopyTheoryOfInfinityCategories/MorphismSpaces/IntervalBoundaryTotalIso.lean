module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalSquareBoundaryFiber
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks

/-!
概要：区間の境界への底変換の全空間は二つの端点 fiber の直和と同型。
方針：境界の各単体が零または一に定値であることを使う。
規約：射影の充填性を要求しない。
使われ方：境界上の指定表現を両端の実際の写像に展開する。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：区間の各端点を境界の頂点として表す。
方針：端点が境界に属する証明を添える。
規約：i=0,1 の両方に同じ定義を使う。
使われ方：境界の二つの fiber への比較。 -/
def intervalBoundaryVertex (i : Fin 2) : (boundary 1 : SSet.{u}) _⦋0⦌ :=
  ⟨stdSimplex.obj₀Equiv.symm i, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.vertex_mem_boundary 0 i⟩

/-- 概要：端点 fiber を境界上の全空間へ写す。
方針：元の fiber の包含と境界頂点への定値射を引き戻す。
規約：元の全空間への包含を厳密に保持する。
使われ方：境界上の表現から端点写像を取り出す。 -/
def intervalBoundaryFiberLift {E : SSet.{u}} (p : E ⟶ (Δ[1] : SSet.{u})) (i : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p (stdSimplex.obj₀Equiv.symm i) ⟶ pullback p (boundary 1).ι :=
  pullback.lift (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p _) (SSet.const (intervalBoundaryVertex i)) (by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.const_comp]
    rfl)

/-- 概要：境界の全空間へ二つの端点 fiber を同時に写す。
方針：各端点の引き戻しへの lift を直和からまとめる。
規約：左右は零、一の順。
使われ方：実際の境界条件と端点条件を比較する同型の順方向。 -/
def intervalBoundaryTotalMap {E : SSet.{u}} (p : E ⟶ (Δ[1] : SSet.{u})) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointDesc (intervalBoundaryFiberLift p 0) (intervalBoundaryFiberLift p 1)

/-- 概要：二端点図式から境界の全空間への比較は元の全空間への包含を保つ。
方針：左右の引き戻しへの lift の第一射影。
規約：厳密な射の一致。
使われ方：境界の pointed space 値の図式を比較する。 -/
lemma intervalBoundaryTotalMap_fst {E : SSet.{u}} (p : E ⟶ (Δ[1] : SSet.{u})) :
    intervalBoundaryTotalMap p ≫ pullback.fst p (boundary 1).ι =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalFiberEndpointInclusion p := by
  apply SSet.hom_ext
  intro n
  ext x
  cases x with
  | inl x =>
    change ((intervalBoundaryFiberLift p 0 ≫ pullback.fst p (boundary 1).ι).app n) x = x.val
    rw [intervalBoundaryFiberLift, pullback.lift_fst]
    rfl
  | inr x =>
    change ((intervalBoundaryFiberLift p 1 ≫ pullback.fst p (boundary 1).ι).app n) x = x.val
    rw [intervalBoundaryFiberLift, pullback.lift_fst]
    rfl

/-- 概要：区間の境界上の全空間は二つの端点 fiber の直和。
方針：比較の単射性と、境界単体の定値性による各次数の全射性を確認する。
規約：空の fiber も許す。
使われ方：境界表現と両端データの厳密な翻訳。 -/
instance intervalBoundaryTotalMap_isIso {E : SSet.{u}}
    (p : E ⟶ (Δ[1] : SSet.{u})) : IsIso (intervalBoundaryTotalMap p) := by
  let : Mono (intervalBoundaryTotalMap p) :=
    mono_of_mono_fac (intervalBoundaryTotalMap_fst p)
  rw [NatTrans.isIso_iff_isIso_app]
  rintro ⟨⟨n⟩⟩
  let d := Opposite.op ⦋n⦌
  rw [isIso_iff_bijective]
  refine ⟨(mono_iff_injective _).mp inferInstance, ?_⟩
  intro y
  let a := (pullback.fst p (boundary 1).ι).app d y
  let b := (pullback.snd p (boundary 1).ι).app d y
  have hp : p.app d a = b.val := ConcreteCategory.congr_hom
    (NatTrans.congr_app (pullback.condition (f := p) (g := (boundary 1).ι)) d) y
  have hb : ∃ i : Fin 2, b.val = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm i) n := by
    refine ⟨b.val 0, ?_⟩
    apply stdSimplex.ext
    intro j
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.boundaryOne_simplex_constant b j
  obtain ⟨i, hi⟩ := hb
  fin_cases i
  · let x : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) _⦋n⦌ :=
      ⟨a, hp.trans hi⟩
    refine ⟨Sum.inl x, ?_⟩
    apply Types.ext_of_isPullback
      ((IsPullback.of_hasPullback p (boundary 1).ι).app d)
    · change ((intervalBoundaryFiberLift p 0 ≫ pullback.fst p (boundary 1).ι).app d) x = a
      rw [intervalBoundaryFiberLift, pullback.lift_fst]
      rfl
    · change ((intervalBoundaryFiberLift p 0 ≫ pullback.snd p (boundary 1).ι).app d) x = b
      rw [intervalBoundaryFiberLift, pullback.lift_snd]
      exact Subtype.ext hi.symm
  · let x : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) _⦋n⦌ :=
      ⟨a, hp.trans hi⟩
    refine ⟨Sum.inr x, ?_⟩
    apply Types.ext_of_isPullback
      ((IsPullback.of_hasPullback p (boundary 1).ι).app d)
    · change ((intervalBoundaryFiberLift p 1 ≫ pullback.fst p (boundary 1).ι).app d) x = a
      rw [intervalBoundaryFiberLift, pullback.lift_fst]
      rfl
    · change ((intervalBoundaryFiberLift p 1 ≫ pullback.snd p (boundary 1).ι).app d) x = b
      rw [intervalBoundaryFiberLift, pullback.lift_snd]
      exact Subtype.ext hi.symm

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
