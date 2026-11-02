module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.ConstantFiberPrism
public import
SerrePositivity.Archive.InfinityCategories.FilteredExchange.DiagonalTwoStepComparisonPrecomp

/-!
概要：元の定値区間の輸送比較は、全係数を制限しても同じ指定値を与える。
方針：同じ実定値 prism の制限と、元の区間比較の制限則を使う。
規約：定値比較と元の始点を保持。使われ方：定値終辺を消去した比較の自然性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 全係数を制限しても、同じ区間の底は元の固定頂点に定値である。 -/
lemma intervalMappingUncurry_precomp_constant {B P Q : SSet.{u}} {a : B _⦋0⦌}
    (c : P ⟶ intervalMappingSpace a a) (hc : intervalMappingUncurry c = SSet.const a)
    (q : Q ⟶ P) : intervalMappingUncurry (q ≫ c) = SSet.const a := by
  rw [intervalMappingUncurry_precomp, hc, SSet.comp_const]

/-- 元の定値輸送比較の制限は、元の始点と区間を制限した定値輸送比較。 -/
lemma diagonalFiberTransport_constantIso_precomp_heq {E B P Q : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] {a : B _⦋0⦌}
    (f : P ⟶ vertexFiber p a) (c : P ⟶ intervalMappingSpace a a)
    (hc : intervalMappingUncurry c = SSet.const a) (q : Q ⟶ P)
    (hc' : intervalMappingUncurry (q ≫ c) = SSet.const a) :
    HEq ((diagonalFiberTransport_constantIso p f c hc).precomp q)
      (diagonalFiberTransport_constantIso p (q ≫ f) (q ≫ c) hc') := by
  have h := leftFibrationPrism_transportIntervalIso_precomp_heq_of_prism p f f c
    (constantFiberPrism p f) (constantFiberPrism_endpoint p f 0)
    (constantFiberPrism_endpoint p f 1) ((constantFiberPrism_projection p f).trans hc.symm)
    q (constantFiberPrism p (q ≫ f)) (constantFiberPrism_endpoint p (q ≫ f) 0)
    (constantFiberPrism_endpoint p (q ≫ f) 1)
    ((constantFiberPrism_projection p (q ≫ f)).trans hc'.symm) (constantFiberPrism_precomp p f q)
  have hsym := vertexIso_symm_heq_of_heq _ _ rfl
    (congrArg functorVertex (diagonalFiberTransport_precomp p f c q)) h
  rw [diagonalFiberTransport_constantIso_eq_prism, diagonalFiberTransport_constantIso_eq_prism,
    functorIso_precomp_symm]
  exact hsym

/-- 同じ元の定値輸送比較は、始点族の厳密な表示変更で値を保つ。 -/
lemma diagonalFiberTransport_constantIso_heq_of_eq {E B P : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] {a : B _⦋0⦌}
    (f f' : P ⟶ vertexFiber p a) (c : P ⟶ intervalMappingSpace a a)
    (hc : intervalMappingUncurry c = SSet.const a) (hf : f = f') :
    HEq (diagonalFiberTransport_constantIso p f c hc)
      (diagonalFiberTransport_constantIso p f' c hc) := by
  cases hf
  rfl

/-- 元の定値比較の制限は、同じ制限後の始点の表示でも元の値を保持する。 -/
lemma diagonalFiberTransport_constantIso_precomp_heq_of_input {E B P Q : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] {a : B _⦋0⦌}
    (f : P ⟶ vertexFiber p a) (c : P ⟶ intervalMappingSpace a a)
    (hc : intervalMappingUncurry c = SSet.const a) (q : Q ⟶ P)
    (hc' : intervalMappingUncurry (q ≫ c) = SSet.const a)
    (f' : Q ⟶ vertexFiber p a) (hf : q ≫ f = f') :
    HEq ((diagonalFiberTransport_constantIso p f c hc).precomp q)
      (diagonalFiberTransport_constantIso p f' (q ≫ c) hc') :=
  (diagonalFiberTransport_constantIso_precomp_heq p f c hc q hc').trans
    (diagonalFiberTransport_constantIso_heq_of_eq p (q ≫ f) f' (q ≫ c) hc' hf)

/-- 元の定値比較は、始点と定値区間の同じ表示変更でも指定値を保つ。 -/
lemma diagonalFiberTransport_constantIso_heq_of_data {E B P : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] {a : B _⦋0⦌}
    (f f' : P ⟶ vertexFiber p a) (c c' : P ⟶ intervalMappingSpace a a)
    (hc : intervalMappingUncurry c = SSet.const a)
    (hc' : intervalMappingUncurry c' = SSet.const a) (hf : f = f') (hcc : c = c') :
    HEq (diagonalFiberTransport_constantIso p f c hc)
      (diagonalFiberTransport_constantIso p f' c' hc') := by
  cases hf
  cases hcc
  rfl

end SerrePositivity.InfinityCategories.F2
