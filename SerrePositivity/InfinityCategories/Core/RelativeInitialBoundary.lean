module

public import SerrePositivity.InfinityCategories.Core.BoundaryOpposite
public import SerrePositivity.InfinityCategories.Core.Cocone
public import SerrePositivity.InfinityCategories.Core.Equivalence
public import SerrePositivity.InfinityCategories.Core.InitialOpposite
public import SerrePositivity.InfinityCategories.Core.Join
public import SerrePositivity.InfinityCategories.Core.JoinBoundary
public import SerrePositivity.InfinityCategories.Core.Opposite
public import SerrePositivity.InfinityCategories.Core.RelativeOuterHornOp
public import SerrePositivity.InfinityCategories.Core.RelativeTerminalExtension
public import SerrePositivity.InfinityCategories.Core.Terminal
public import SerrePositivity.InfinityCategories.Core.VertexFiber
public import SerrePositivity.InfinityCategories.PinchedHom.Basic
public import SerrePositivity.InfinityCategories.Core.CoconeFamily
public import SerrePositivity.InfinityCategories.Core.ColimitCoconeFamily
public import Mathlib.Tactic.CrossRefAttribute

/-! # 相対始対象の境界充填

概要：射の上で最初の頂点を固定した境界を充填する条件を終点版と比較する。
方針：標準単体と境界を反転し、指定した標的の単体を保って戻す。
規約：ファイブレーション性は定義に含めない。使われ方：普遍余錐の相対充填。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：始点 x の正次元境界を指定された標的の単体の上で充填できる条件。
方針：全ての境界の可換正方形に持ち上げを要求する。
規約：inner fibration 性や quasicategory 性は含めない。使われ方：相対始対象の判定。 -/
def InitialBoundaryLifting {X Y : SSet.{u}} (p : X ⟶ Y) (x : X _⦋0⦌) : Prop :=
  ∀ (n : ℕ) (a : (boundary (n + 1) : SSet.{u}) ⟶ X) (b : (Δ[n + 1] : SSet.{u}) ⟶ Y),
    boundaryVertex n 0 ≫ a = SSet.yonedaEquiv.symm x →
      CommSq a (boundary (n + 1)).ι p b →
        ∃ F : (Δ[n + 1] : SSet.{u}) ⟶ X, (boundary (n + 1)).ι ≫ F = a ∧ F ≫ p = b

/-- 概要：反転した射の終点境界充填から元の射の始点境界充填が得られる。
方針：全ての境界と標的の単体を反転し、持ち上げを反転して戻す。
規約：quasicategory 性は不要。使われ方：相対終対象の定理の双対化。 -/
lemma initialBoundaryLifting_of_terminalBoundaryLifting_op {E B : SSet.{u}}
    (p : E ⟶ B) (x : E _⦋0⦌)
    (hx : TerminalBoundaryLifting (SSet.opFunctor.map p) (SSet.opObjEquiv.symm x)) :
    InitialBoundaryLifting p x := by
  intro n a b hfirst sq
  have hlast : boundaryVertex n (Fin.last (n + 1)) ≫ reverseBoundaryMap (n + 1) a =
      SSet.yonedaEquiv.symm (SSet.opObjEquiv.symm x) := by
    rw [reverseBoundaryMap_vertex, Fin.rev_last, hfirst, reverseSimplex_vertex]
  have sq' : CommSq (reverseBoundaryMap (n + 1) a) (boundary (n + 1)).ι
      (SSet.opFunctor.map p) (reverseSimplex (n + 1) b) := by
    constructor
    rw [← reverseBoundaryMap_comp, sq.w, reverseBoundaryMap_restrict]
  obtain ⟨F, hF, hFp⟩ := hx n _ _ hlast sq'
  let G := reverseSimplex (n + 1) F ≫ (SSet.opFunctorCompOpFunctorIso.app E).hom
  refine ⟨G, ?_, ?_⟩
  · apply reverseBoundaryMap_injective E (n + 1)
    rw [reverseBoundaryMap_restrict, reverseSimplex_back]
    exact hF
  · apply reverseSimplex_injective B (n + 1)
    rw [reverseSimplex_comp, reverseSimplex_back]
    exact hFp

/-- 概要：射の上で始点境界を充填できる頂点は、その fiber の始対象である。
方針：標的の単体を定値に取る。
規約：ファイブレーション性は不要。使われ方：相対条件から余極限性へ戻す。 -/
@[kerodon 02WV]
lemma InitialBoundaryLifting.isInitialVertex_fiber {E B : SSet.{u}}
    (p : E ⟶ B) (b : B _⦋0⦌) (x : (vertexFiber p b) _⦋0⦌)
    (hx : InitialBoundaryLifting p x.val) : IsInitialVertex x := by
  intro n a ha
  have hfirst : boundaryVertex n 0 ≫ (a ≫ vertexFiberι p b) =
      SSet.yonedaEquiv.symm x.val := by
    rw [← Category.assoc, ha, SSet.yonedaEquiv_symm_comp]
    rfl
  have sq : CommSq (a ≫ vertexFiberι p b) (boundary (n + 1)).ι p (SSet.const b) := by
    constructor
    rw [Category.assoc, vertexFiberι_comp, SSet.comp_const, SSet.comp_const]
  obtain ⟨F, hF, hFp⟩ := hx n _ _ hfirst sq
  refine ⟨vertexFiberLift p b F hFp, ?_⟩
  apply vertexFiber_hom_ext p b
  rw [Category.assoc, vertexFiberLift_ι]
  exact hF

/-- 概要：余錐の制限射の上で始点境界を充填できる余錐は余極限錐である。
方針：固定図式上の余錐の族の始対象性へ制限する。
規約：値域は quasicategory。逆方向は別の定理を必要とする。
使われ方：相対的な普遍性から余極限性への接続。 -/
@[kerodon 02XD]
lemma isColimitCone_of_initialBoundaryLifting_coconeRestriction
    {K X : SSet.{u}} [Quasicategory X] {p : K ⟶ X} (c : JoinCocone p)
    (hc : InitialBoundaryLifting (coconeRestriction K X) (functorVertex c.val)) :
    IsColimitCone c := by
  apply (isColimitCone_iff_isInitialVertex_coconeFamily c).2
  exact InitialBoundaryLifting.isInitialVertex_fiber (coconeRestriction K X) (functorVertex p)
    (coconeFamilyVertexEquiv p c) hc

end SerrePositivity.InfinityCategories
