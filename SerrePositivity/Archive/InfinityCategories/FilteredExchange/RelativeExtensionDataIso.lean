module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.ContractibleVertexIsoNaturality
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.RelativeFunctorExtensionSpace

/-!
概要：底と初期値の等式で、同じ実延長を保つ同型を構成する。
方針：元の全単体を保持し、底と初期値の証明成分だけを更新する。
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
  (v v' : D ⟶ E) (hv : v ≫ p = i ≫ b) (hv' : v' ≫ p = i ≫ b')
  (h : b = b') (he : v = v')

/-- 底と初期値の等式で証明成分だけを更新し、元の全単体を保つ射。 -/
def relativeExtensionDataMap :
    relativeFunctorExtensionSpace p b i v hv ⟶ relativeFunctorExtensionSpace p b' i v' hv' where
  app _ := ↾fun x => ⟨⟨x.val.val, by subst b'; exact x.val.property⟩,
    by subst b'; subst v'; exact x.property⟩
  naturality _ _ _ := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    apply Subtype.ext
    rfl

/-- 底と初期値の等式による、元の全延長を保つ厳密な同型。 -/
def relativeExtensionDataIso :
    relativeFunctorExtensionSpace p b i v hv ≅ relativeFunctorExtensionSpace p b' i v' hv' where
  hom := relativeExtensionDataMap p b b' i v v' hv hv' h he
  inv := relativeExtensionDataMap p b' b i v' v hv' hv h.symm he.symm
  hom_inv_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    apply Subtype.ext
    rfl
  inv_hom_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    apply Subtype.ext
    rfl

/-- 底と初期値の移送は、元の全延長の内部 Hom 成分を厳密に保持する。 -/
lemma relativeExtensionDataIso_vertex_value
    (x : (relativeFunctorExtensionSpace p b i v hv) _⦋0⦌) :
    (((relativeExtensionDataIso p b b' i v v' hv hv' h he).hom.app (Opposite.op ⦋0⦌) x).val).val =
      x.val.val := rfl

/-- 同じ指定同型を底と初期値の等式で移し、両端の実頂点を明示する。 -/
def relativeExtensionDataIso_map
    {x y : (relativeFunctorExtensionSpace p b i v hv) _⦋0⦌} (e : VertexIso x y) :
    VertexIso
      ((relativeExtensionDataIso p b b' i v v' hv hv' h he).hom.app (Opposite.op ⦋0⦌) x)
      ((relativeExtensionDataIso p b b' i v v' hv hv' h he).hom.app (Opposite.op ⦋0⦌) y) :=
  VertexIso.map e (relativeExtensionDataIso p b b' i v v' hv hv' h he).hom

/-- 底と初期値の移送後も指定同型の像は同じ可縮な延長空間の標準比較となる。 -/
lemma relativeExtensionDataIso_vertexIso [LeftFibration p] (hi : leftAnodyneExtensions i)
    {x y : (relativeFunctorExtensionSpace p b i v hv) _⦋0⦌} (e : VertexIso x y) :
    VertexIso.map e (relativeExtensionDataIso p b b' i v v' hv hv' h he).hom =
      (relativeFunctorExtensionSpace_isContractibleKan p b' i hi v' hv').vertexIso
        ((relativeExtensionDataIso p b b' i v v' hv hv' h he).hom.app (Opposite.op ⦋0⦌) x)
        ((relativeExtensionDataIso p b b' i v v' hv hv' h he).hom.app (Opposite.op ⦋0⦌) y) :=
  vertexIso_map_eq_contractible
    (relativeFunctorExtensionSpace_isContractibleKan p b' i hi v' hv') e _

end SerrePositivity.InfinityCategories.F2
