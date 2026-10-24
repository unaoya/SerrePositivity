module

public import SerrePositivity.InfinityCategories.F2.Presentable.DiscreteDiagramVertices
public import SerrePositivity.InfinityCategories.F2.Presentable.SigmaFiniteFamilyComparisonDetection

/-!
概要：Yoneda 像からなる離散図式を、元の小さい底の実際の離散図式へ戻す。
方針：成分頂点から離散図式を構成し、頂点外延性で元の図式を回収する。
規約：元の小さい宇宙の底と元の Yoneda を使う。
使われ方：元の Yoneda 制限上の有限余積条件の全比較への適用。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits

/-- 概要：元の小さい成分頂点族から元の離散全図式を作る。
方針：各離散単体を同じ頂点の定値退化へ送る。
規約：全単体の自然性を保持する。
使われ方：Yoneda 像上の図式の小さい底での回収。 -/
def discreteDiagramFromVertices {I : Type u} {X : SSet.{u}} (f : I → X _⦋0⦌) :
    nerve (Discrete I) ⟶ X where
  app n := ↾fun s ↦ PinchedHom.constant (f (discreteNerveComponent s)) n.unop.len
  naturality {n m} α := by
    apply ConcreteCategory.hom_ext
    intro s
    change PinchedHom.constant (f (discreteNerveComponent
      ((nerve (Discrete I)).map α s))) m.unop.len =
      X.map α (PinchedHom.constant (f (discreteNerveComponent s)) n.unop.len)
    rw [discreteNerveComponent_map]
    exact (PinchedHom.constant_pullback _ α.unop).symm

/-- 概要：構成した離散全図式は元の指定頂点を回収する。
方針：零次の定値退化の値を計算する。
規約：同じ小さい成分を使う。
使われ方：Yoneda 因子化の頂点条件。 -/
lemma discreteDiagramFromVertices_vertex {I : Type u} {X : SSet.{u}}
    (f : I → X _⦋0⦌) (i : I) :
    (discreteDiagramFromVertices f).app (Opposite.op ⦋0⦌) (nerveVertex (Discrete.mk i)) = f i :=
  pinchedConstant_zero _

/-- 概要：全成分が Yoneda 像の離散全図式は元の小さい離散図式から因子化する。
方針：各成分の元の底頂点を選び、全図式の頂点外延性を使う。
規約：他の圏で生成対象を選び直さない。
使われ方：元の有限余積条件を全関手比較の基準図式へ適用する。 -/
lemma sigmaYonedaFamily_factorization {I : Type u} {C : SSet.{u}} [Quasicategory C]
    (p : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (Discrete I)) ⟶ SigmaPresheafInfinity C)
    (hp : IsSigmaYonedaFamilyOutside C ∅ p) :
    ∃ q : nerve (Discrete I) ⟶ C,
      (SSet.uliftFunctor.{u + 1, u}).map q ≫ sigmaYonedaInfinityMap C = p := by
  classical
  have hf (i : I) := hp i (by simp)
  let f : I → C _⦋0⦌ := fun i ↦ (Classical.choose (hf i)).down
  refine ⟨discreteDiagramFromVertices f, ?_⟩
  apply liftedDiscreteDiagram_hom_ext
  intro i
  change (sigmaYonedaInfinityMap C).app (Opposite.op ⦋0⦌)
    (ULift.up ((discreteDiagramFromVertices f).app (Opposite.op ⦋0⦌)
      (nerveVertex (Discrete.mk i)))) = _
  rw [discreteDiagramFromVertices_vertex]
  exact (Classical.choose_spec (hf i)).symm

end SerrePositivity.InfinityCategories.F2.Presentable
