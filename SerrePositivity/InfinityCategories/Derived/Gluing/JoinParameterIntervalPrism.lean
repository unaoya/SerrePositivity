module
public import SerrePositivity.InfinityCategories.Derived.Gluing.JoinParameterComparison
public import SerrePositivity.InfinityCategories.F1.MappingSpacePrisms
public import SerrePositivity.InfinityCategories.Core.JoinCylinderSimplex

/-! 点との join による辺族は、既存の pinched Hom 用区間 prism と同じ全単体を持つ。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial

lemma dgGluingAugPoint_subsingleton (r : ℕ) :
    Subsingleton (Join.augObj (Δ[0] : SSet.{u}) r) := by
  cases r with
  | zero => dsimp only [Join.augObj]; infer_instance
  | succ r =>
    dsimp only [Join.augObj]
    refine ⟨fun a b => ?_⟩
    apply stdSimplex.ext
    intro i
    apply Fin.ext
    have ha := (a i).isLt
    have hb := (b i).isLt
    omega

lemma dgGluingJoinParameterIntervalPrism (K : SSet.{u}) :
    ((joinStdSimplexIso 0 0).inv ▷ K) ≫
        dgGluingJoinParameterComparison Δ[0] Δ[0] K ≫
        joinMap (snd (Δ[0] : SSet.{u}) K) (𝟙 Δ[0]) = rightMappingSpacePrism K := by
  have hp : joinMap (β_ K (Δ[0] : SSet.{u})).hom (𝟙 Δ[0]) ≫
      joinMap (snd (Δ[0] : SSet.{u}) K) (𝟙 Δ[0]) = joinMap (fst K Δ[0]) (𝟙 Δ[0]) := by
    rw [← joinMap_comp, Category.id_comp]
    rfl
  rw [dgGluingJoinParameterComparison, Category.assoc, Category.assoc, hp]
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨t, k⟩
  let s := (joinStdSimplexIso.{u} 0 0).inv.app (Opposite.op ⦋n⦌) t
  let b := PinchedHom.constant (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) n
  change (joinMap (fst K (Δ[0] : SSet.{u})) (𝟙 Δ[0])).app (Opposite.op ⦋n⦌)
      (Join.tensorLeftSimplex K Δ[0] Δ[0] n k s) =
    (joinCylinderMap K Δ[0]).app (Opposite.op ⦋n⦌) ((k, t), b)
  rw [joinCylinderMap_app]
  change (⟨s.1, Join.augHom (fst K (Δ[0] : SSet.{u})) s.1.val
      ((Join.augTensorEquiv K Δ[0] s.1.val).symm
        (Join.augMap K (Join.prefixIncl (n + 1) s.1.val
          (Nat.le_of_lt_succ s.1.isLt)) k, s.2.1)),
      Join.augHom (𝟙 (Δ[0] : SSet.{u})) (n + 1 - s.1.val) s.2.2⟩ : Join.Simplex K Δ[0] n) =
    ⟨s.1, Join.augMap K (Join.prefixIncl (n + 1) s.1.val
        (Nat.le_of_lt_succ s.1.isLt)) k,
      Join.augMap Δ[0] (Join.suffixIncl (n + 1) s.1.val
        (Nat.le_of_lt_succ s.1.isLt)) b⟩
  rw [Join.augTensorEquiv_symm_augHomFst]
  refine Join.Simplex.ext _ _ rfl ?_ ?_
  · rfl
  · have := dgGluingAugPoint_subsingleton.{u} (n + 1 - s.1.val)
    exact Subsingleton.elim _ _

end SerrePositivity.InfinityCategories
