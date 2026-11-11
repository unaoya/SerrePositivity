module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.RelativeExtensionFiberEndpoint
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.VertexIsoCompositionTransport

/-!
概要：元の fiber 終点の指定比較を、元の可縮な全延長空間の比較の像へ値まで戻す。
方針：既存の比較の終点表示の等式による移送だけを除く。
規約：元の延長と指定比較を保持。使われ方：下側輸送因子の選択比較の厳密な合成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の fiber 終点の指定比較は、元の全延長空間の指定同型を同じ終点で評価した値。 -/
lemma relativeExtensionFiberEndpoint_witnessIso_heq_map {A D C E B : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (a : A ⟶ B) (i : D ⟶ A)
    (hi : leftAnodyneExtensions i) (v : D ⟶ E) (hv : v ≫ p = i ≫ a)
    (j : C ⟶ A) (b : B _⦋0⦌) (hj : j ≫ a = SSet.const b)
    (W W' : A ⟶ E) (hW : W ≫ p = a) (hW' : W' ≫ p = a)
    (hWi : i ≫ W = v) (hWi' : i ≫ W' = v)
    (g g' : C ⟶ vertexFiber p b)
    (hWj : j ≫ W = g ≫ vertexFiberι p b) (hWj' : j ≫ W' = g' ≫ vertexFiberι p b) :
    HEq (relativeExtensionFiberEndpoint_witnessIso p a i hi v hv j b hj
      W W' hW hW' hWi hWi' g g' hWj hWj')
      (VertexIso.map ((relativeFunctorExtensionSpace_isContractibleKan p a i hi v hv).vertexIso
        (relativeFunctorExtensionSpaceVertexEquiv p a i v hv ⟨W, hW, hWi⟩)
        (relativeFunctorExtensionSpaceVertexEquiv p a i v hv ⟨W', hW', hWi'⟩))
        (relativeExtensionFiberEndpoint p a i v hv j b hj)) := by
  unfold relativeExtensionFiberEndpoint_witnessIso
  have hcast {α β : Sort (u + 1)} (h : α = β) (e : α) : HEq (Eq.mp h e) e := by
    cases h
    rfl
  dsimp only
  refine (hcast _ _).trans ?_
  exact hcast _ _

end SerrePositivity.InfinityCategories.F2
