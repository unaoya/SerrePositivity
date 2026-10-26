module

public import SerrePositivity.InfinityCategories.F1.Diagrams.TrianglePrismLiftedSection

/-!
概要：固定した K の頂点上で、長 Hom から全区間・全高次パラメーターを回収する。
方針：補助単体を二段退化させ、native path の二座標の厳密な切断を前合成する。
規約：任意の次数 n と補助単体 r に対する全族の等号。
使われ方：実 encoder の単射性の検討で、頂点データを高次パラメーターへ拡張する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SimplicialThickening MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

lemma triangleSeparatedLongHom_prism_recovery
    {K L : SSet.{max u v}} {H : SSet.{u}}
    (M : (Δ[1] : SSet.{max u v}) ⊗ ((K ⊗ K) ⊗ L) ⟶ (SSet.uliftFunctor.{v, u}).obj H)
    (q : (Δ[1] : SSet.{max u v}) ⊗ (K ⊗ L) ⟶ (SSet.uliftFunctor.{v, u}).obj H)
    (hdiag : (Δ[1] ◁ triangleParameterDiagonal K L) ≫ M = q)
    (k : K _⦋0⦌) (n : ℕ) (r : L _⦋n⦌) :
    trianglePrismLiftedSection.{u, v} n ≫ (SSet.uliftFunctor.{v, u}).map
      (triangleSeparatedLongHom M (PinchedHom.constant k (n + 2))
        (L.map (SimplexCategory.mkHom (trianglePrismRetraction n)).op r)
        (trianglePrismLabel n) (trianglePrismLabel_zero n) (Fin.last (n + 2))) =
      lift (fst (Δ[1] : SSet.{max u v}) Δ[n])
        (lift (SSet.const k) (snd Δ[1] Δ[n] ≫ SSet.yonedaEquiv.symm r)) ≫ q := by
  rw [triangleSeparatedLongHom_vertex_parameter M q hdiag]
  rw [← Category.assoc]
  apply congrArg (fun z => z ≫ q)
  rw [comp_lift, comp_lift, trianglePrismLiftedSection_middle,
    trianglePrismLiftedSection_parameter, SSet.comp_const]

end SerrePositivity.InfinityCategories
