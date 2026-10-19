module

public import SerrePositivity.InfinityCategories.HomotopyLimits.FixedExtensionCurry
public import SerrePositivity.InfinityCategories.Core.KanHomotopyEquivalence

/-!
概要：底と初期値を固定する実際の円柱を、同じ相対延長空間の辺へ戻す。
方針：円柱を固定延長空間へ curry し、両端を元の実際の延長の頂点と照合する。
規約：辺も円柱も代表を選び直さない。
使われ方：指定した輸送比較を可縮な延長空間の高次比較へ接続する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {A D E B : SSet.{u}} (p : E ⟶ B) (β : A ⟶ B) (i : D ⟶ A)
  (v : D ⟶ E) (hv : v ≫ p = i ≫ β)
  {W W' : A ⟶ E} (hW : W ≫ p = β) (hW' : W' ≫ p = β)
  (hWi : i ≫ W = v) (hWi' : i ≫ W' = v)
  (H : SSet.Homotopy W W') (hH : H.h ≫ p = fst A (Δ[1] : SSet.{u}) ≫ β)
  (hI : (i ▷ (Δ[1] : SSet.{u})) ≫ H.h = fst D (Δ[1] : SSet.{u}) ≫ v)

/-- 同じ実際の円柱を表す、固定延長空間内の辺。 -/
def fixedExtensionHomotopyEdge :
    (relativeFunctorExtensionSpace p β i v hv).Edge
      (relativeFunctorExtensionSpaceVertexEquiv p β i v hv ⟨W, hW, hWi⟩)
      (relativeFunctorExtensionSpaceVertexEquiv p β i v hv ⟨W', hW', hWi'⟩) where
  edge := SSet.yonedaEquiv (fixedExtensionCurry p β i v hv H.h hH hI)
  src_eq := by
    change (relativeFunctorExtensionSpace p β i v hv).δ 1 (SSet.yonedaEquiv _) = _
    rw [← stdSimplex.yonedaEquiv_δ_comp, SSet.yonedaEquiv_comp]
    have hx : SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 2) :
        (Δ[0] : SSet.{u}) ⟶ Δ[1]) = stdSimplex.obj₀Equiv.symm 0 := by decide
    rw [hx, fixedExtensionCurry_vertex]
    apply Subtype.ext
    apply Subtype.ext
    change functorVertex (SSet.ι₀ ≫ H.h) = functorVertex W
    rw [H.h₀]
  tgt_eq := by
    change (relativeFunctorExtensionSpace p β i v hv).δ 0 (SSet.yonedaEquiv _) = _
    rw [← stdSimplex.yonedaEquiv_δ_comp, SSet.yonedaEquiv_comp]
    have hx : SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2) :
        (Δ[0] : SSet.{u}) ⟶ Δ[1]) = stdSimplex.obj₀Equiv.symm 1 := by decide
    rw [hx, fixedExtensionCurry_vertex]
    apply Subtype.ext
    apply Subtype.ext
    change functorVertex (SSet.ι₁ ≫ H.h) = functorVertex W'
    rw [H.h₁]

/-- 延長空間内の辺を展開すると、指定した元の円柱そのものになる。 -/
lemma fixedExtensionHomotopyEdge_uncurry :
    relativeFunctorUncurry
      (SSet.yonedaEquiv.symm (fixedExtensionHomotopyEdge p β i v hv
        hW hW' hWi hWi' H hH hI).edge ≫ relativeFunctorExtensionSpaceι p β i v hv) = H.h := by
  change relativeFunctorUncurry
    (SSet.yonedaEquiv.symm (SSet.yonedaEquiv _) ≫ relativeFunctorExtensionSpaceι p β i v hv) = _
  rw [Equiv.symm_apply_apply, fixedExtensionCurry_uncurry]

/-- 忘却後の辺も、元の円柱を curry した関手辺を全単体で保つ。 -/
lemma fixedExtensionHomotopyEdge_projection :
    SSet.yonedaEquiv.symm (fixedExtensionHomotopyEdge p β i v hv
      hW hW' hWi hWi' H hH hI).edge ≫ relativeFunctorExtensionSpaceι p β i v hv ≫
        vertexFiberι ((ihom A).map p) (functorVertex β) = curry H.h := by
  change SSet.yonedaEquiv.symm (SSet.yonedaEquiv _) ≫ _ = _
  rw [Equiv.symm_apply_apply, ← Category.assoc, fixedExtensionCurry_ι]
  exact vertexFiberLift_ι _ _ _ _

end
end SerrePositivity.InfinityCategories.HomotopyLimits
