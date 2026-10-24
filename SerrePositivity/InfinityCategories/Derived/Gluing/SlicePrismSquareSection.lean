module
public import SerrePositivity.InfinityCategories.Derived.Gluing.SlicePrismTriangle
public import SerrePositivity.InfinityCategories.F1.Coherent.PrismEvaluation
/-!
概要：slice prism の全三角形を同じ二時間の正方形の一片として回収する。
方針：三頂点を (0,0)、(0,1)、(1,1) へ写し、右 join prism の標準切断を使う。
規約：全パラメーターを第一 join 因子に保持する。
使われ方：第二単位の全 coherent 図式表示を全三角形の退化へ移す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial

def dgGluingTriangleSquareSection : (Δ[2] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1] :=
  lift (stdSimplex.σ (0 : Fin 2)) (stdSimplex.σ (1 : Fin 2))

lemma dgGluingTriangleSquareSection_prism :
    dgGluingTriangleSquareSection.{u} ≫ rightMappingSpacePrism Δ[1] =
      (joinStdSimplexIso 1 0).inv := by
  apply (cancel_mono (joinStdSimplexIso 1 0).hom).mp
  rw [Iso.inv_hom_id]
  apply SSet.yonedaEquiv.injective
  apply SSet.stdSimplex.ext
  intro i
  fin_cases i <;> rfl

lemma dgGluingJoinParameterComparison_prism (A K : SSet.{u}) :
    (rightMappingSpacePrism A ▷ K) ≫ dgGluingJoinParameterComparison A Δ[0] K =
      (α_ Δ[1] A K).hom ≫ rightMappingSpacePrism (A ⊗ K) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨⟨t, a⟩, k⟩
  change (dgGluingJoinParameterComparison A Δ[0] K).app _
    ((joinCylinderMap A Δ[0]).app _ ((a, t),
      (SSet.const (X := Δ[1] ⊗ A) (stdSimplex.obj₀Equiv.symm 0)).app _ (t, a)), k) =
    (joinCylinderMap (A ⊗ K) Δ[0]).app _ (((a, k), t),
      (SSet.const (X := Δ[1] ⊗ (A ⊗ K)) (stdSimplex.obj₀Equiv.symm 0)).app _ (t, (a, k)))
  rw [joinCylinderMap_app, joinCylinderMap_app]
  let cut := (joinStdSimplexIso.{u} 0 0).inv.app (Opposite.op ⦋n⦌) t
  change (⟨cut.1,
    Join.augHom (β_ K A).hom cut.1.val
      ((Join.augTensorEquiv K A cut.1.val).symm
        (Join.augMap K (Join.prefixIncl (n + 1) cut.1.val _) k,
          Join.augMap A (Join.prefixIncl (n + 1) cut.1.val _) a)),
    Join.augHom (𝟙 Δ[0]) (n + 1 - cut.1.val) _⟩ : Join.Simplex (A ⊗ K) Δ[0] n) = _
  have hpair (r : ℕ) (α : Fin r →o Fin (n + 1)) :
      Join.augHom (β_ K A).hom r
        ((Join.augTensorEquiv K A r).symm (Join.augMap K α k, Join.augMap A α a)) =
      Join.augMap (A ⊗ K) α (a, k) := by
    cases r <;> rfl
  have hpoint (r : ℕ) (a b : Join.augObj (Δ[0] : SSet.{u}) r) : a = b := by
    cases r with
    | zero =>
      change PUnit at a b
      cases a
      cases b
      rfl
    | succ r =>
      apply SSet.stdSimplex.ext
      intro i
      apply Fin.ext
      omega
  refine Join.Simplex.ext _ _ rfl ?_ ?_
  · exact hpair _ _
  · exact hpoint _ _ _

lemma dgGluingSlicePrismTriangle_square_section {K X : SSet.{u}}
    {p : (Δ[0] : SSet.{u}) ⟶ X} (s : (Δ[1] : SSet.{u}) ⊗ K ⟶ sliceOver p) :
    dgGluingSlicePrismTriangle s =
      (dgGluingTriangleSquareSection ▷ K) ≫ (α_ Δ[1] Δ[1] K).hom ≫
        rightMappingSpacePrism (Δ[1] ⊗ K) ≫ sliceOverUncurry s := by
  rw [dgGluingSlicePrismTriangle, ← dgGluingTriangleSquareSection_prism,
    comp_whiskerRight, Category.assoc, reassoc_of% dgGluingJoinParameterComparison_prism]
end SerrePositivity.InfinityCategories
