module

public import SerrePositivity.InfinityCategories.F2.ContractibleVertexIsoNaturality
public import SerrePositivity.InfinityCategories.F2.RelativeExtensionDataIso

/-!
概要：底の図式の等式で、始点固定の延長空間を同型に移す。
方針：底だけの等式を消去し、同じ全延長と指定同型の値を保持する。
規約：実延長の証拠全体を選び直さない。使われ方：左右の長辺を共通の底へ揃える。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {A D E B : SSet.{u}} (p : E ⟶ B) (b b' : A ⟶ B) (i : D ⟶ A)
  (v : D ⟶ E) (hv : v ≫ p = i ≫ b) (hv' : v ≫ p = i ≫ b') (h : b = b')

/-- 底の等式で証明成分だけを更新し、元の全単体を保つ射。 -/
def relativeExtensionBaseMap :
    relativeFunctorExtensionSpace p b i v hv ⟶ relativeFunctorExtensionSpace p b' i v hv' :=
  relativeExtensionDataMap p b b' i v v hv hv' h rfl

/-- 底の図式の等式による、同じ始点付き延長空間の厳密な同型。 -/
def relativeExtensionBaseIso :
    relativeFunctorExtensionSpace p b i v hv ≅ relativeFunctorExtensionSpace p b' i v hv' :=
  relativeExtensionDataIso p b b' i v v hv hv' h rfl

/-- 底の移送は、元の全延長の内部 Hom 成分を厳密に保持する。 -/
lemma relativeExtensionBaseIso_vertex_value
    (x : (relativeFunctorExtensionSpace p b i v hv) _⦋0⦌) :
    (((relativeExtensionBaseIso p b b' i v hv hv' h).hom.app (Opposite.op ⦋0⦌) x).val).val =
      x.val.val := rfl

/-- 底の移送後の実延長は元の同じ射を表す。 -/
lemma relativeExtensionBaseIso_vertex (W : A ⟶ E) (hW : W ≫ p = b) (hWi : i ≫ W = v) :
    (relativeExtensionBaseIso p b b' i v hv hv' h).hom.app (Opposite.op ⦋0⦌)
      (relativeFunctorExtensionSpaceVertexEquiv p b i v hv ⟨W, hW, hWi⟩) =
    relativeFunctorExtensionSpaceVertexEquiv p b' i v hv' ⟨W, hW.trans h, hWi⟩ := by
  apply Subtype.ext
  apply Subtype.ext
  rfl

/-- 同じ指定同型を底だけの等式で移し、両端の実頂点を明示する。 -/
def relativeExtensionBaseIso_map
    {x y : (relativeFunctorExtensionSpace p b i v hv) _⦋0⦌} (e : VertexIso x y) :
    VertexIso
      ((relativeExtensionBaseIso p b b' i v hv hv' h).hom.app (Opposite.op ⦋0⦌) x)
      ((relativeExtensionBaseIso p b b' i v hv hv' h).hom.app (Opposite.op ⦋0⦌) y) :=
  VertexIso.map e (relativeExtensionBaseIso p b b' i v hv hv' h).hom

/-- 底の移送後も指定同型の像は同じ可縮な延長空間の標準比較となる。 -/
lemma relativeExtensionBaseIso_vertexIso [LeftFibration p] (hi : leftAnodyneExtensions i)
    {x y : (relativeFunctorExtensionSpace p b i v hv) _⦋0⦌} (e : VertexIso x y) :
    VertexIso.map e (relativeExtensionBaseIso p b b' i v hv hv' h).hom =
      (relativeFunctorExtensionSpace_isContractibleKan p b' i hi v hv').vertexIso
        ((relativeExtensionBaseIso p b b' i v hv hv' h).hom.app (Opposite.op ⦋0⦌) x)
        ((relativeExtensionBaseIso p b b' i v hv hv' h).hom.app (Opposite.op ⦋0⦌) y) :=
  vertexIso_map_eq_contractible
    (relativeFunctorExtensionSpace_isContractibleKan p b' i hi v hv') e _

end SerrePositivity.InfinityCategories.F2
