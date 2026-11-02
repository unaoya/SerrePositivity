module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeFixedExtensionHomotopyEdge
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeFixedExtensionEndpointCylinder

/-!
概要：元の固定延長の実辺を終点評価で写すと同じ実円柱の制限を回収する。
方針：同じ辺の Yoneda 表示と同じ curry の往復を使う。
規約：元の両端・図式・部分族の固定条件を全て保持する。
使われ方：既存の指定比較の終点像の実代表の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の固定円柱から作る実辺の Yoneda 射は同じ curry そのもの。 -/
lemma relativeFixedExtensionHomotopyEdge_yoneda {D A E B : SSet.{u}}
    (p : E ⟶ B) (b : A ⟶ B) (i : D ⟶ A) (v : D ⟶ E)
    (hv : v ≫ p = i ≫ b) {f g : A ⟶ E} (H : SSet.Homotopy f g)
    (hf : f ≫ p = b) (hg : g ≫ p = b) (hif : i ≫ f = v) (hig : i ≫ g = v)
    (hB : H.h ≫ p = fst A Δ[1] ≫ b) (hV : (i ▷ Δ[1]) ≫ H.h = fst D Δ[1] ≫ v) :
    SSet.yonedaEquiv.symm
      (relativeFixedExtensionHomotopyEdge p b i v hv H hf hg hif hig hB hV).edge =
        relativeFixedExtensionCurry p b i v hv H.h hB hV :=
  Equiv.symm_apply_apply _ _

/-- 同じ固定延長の実辺の fiber 終点像は元の実円柱の制限そのもの。 -/
lemma relativeFixedExtensionHomotopyEdge_endpoint_uncurry {D A C E B : SSet.{u}}
    (p : E ⟶ B) (b : A ⟶ B) (i : D ⟶ A) (v : D ⟶ E)
    (hv : v ≫ p = i ≫ b) {f g : A ⟶ E} (H : SSet.Homotopy f g)
    (hf : f ≫ p = b) (hg : g ≫ p = b) (hif : i ≫ f = v) (hig : i ≫ g = v)
    (hB : H.h ≫ p = fst A Δ[1] ≫ b) (hV : (i ▷ Δ[1]) ≫ H.h = fst D Δ[1] ≫ v)
    (j : C ⟶ A) (y : B _⦋0⦌) (hy : j ≫ b = SSet.const y) :
    uncurry (SSet.yonedaEquiv.symm
      (((relativeFixedExtensionHomotopyEdge p b i v hv H hf hg hif hig hB hV).map
        (relativeExtensionFiberEndpoint p b i v hv j y hy)).edge)) ≫ vertexFiberι p y =
          (j ▷ Δ[1]) ≫ H.h := by
  change uncurry (SSet.yonedaEquiv.symm
    ((relativeExtensionFiberEndpoint p b i v hv j y hy).app (Opposite.op ⦋1⦌)
      (relativeFixedExtensionHomotopyEdge p b i v hv H hf hg hif hig hB hV).edge)) ≫ _ = _
  rw [← SSet.yonedaEquiv_symm_comp,
    relativeFixedExtensionHomotopyEdge_yoneda p b i v hv H hf hg hif hig hB hV]
  exact relativeFixedExtensionCurry_endpoint_uncurry p b i v hv H.h hB hV j y hy

end SerrePositivity.InfinityCategories.F2
