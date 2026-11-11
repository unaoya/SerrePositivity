module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpacePrisms
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.JoinCylinderSimplex

/-!
概要：元の右 join prism と全係数の追加が、同じ切断上で厳密に両立する。
方針：先頭に制限した二因子を交換し、補った直積の比較を使う。
規約：全係数を保持。使われ方：標準三角形錐と元の実三角形の同定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 同じ補った直積の交換は、元の二係数を同じ切断で交換する。 -/
lemma augHom_braiding_tensor (A P : SSet.{u}) (r : ℕ)
    (a : Join.augObj A r) (p : Join.augObj P r) :
    Join.augHom (β_ P A).hom r ((Join.augTensorEquiv P A r).symm (p, a)) =
      (Join.augTensorEquiv A P r).symm (a, p) := by
  cases r <;> rfl

/-- 元の実錐の左因子へ、同じ全係数を追加する。 -/
def rightConeCoefficient (A P : SSet.{u}) : P ⊗ join A Δ[0] ⟶ join (A ⊗ P) Δ[0] :=
  joinTensorLeft P A Δ[0] ≫ joinMap (β_ P A).hom (𝟙 Δ[0])

/-- 元の右 prism は、同じ実錐への全係数の追加として厳密に計算できる。 -/
lemma rightMappingSpacePrism_coefficient (A P : SSet.{u}) :
    rightMappingSpacePrism (A ⊗ P) =
      lift (snd _ _ ≫ snd _ _) (lift (fst _ _) (snd _ _ ≫ fst _ _)) ≫
        (P ◁ rightMappingSpacePrism A) ≫ rightConeCoefficient A P := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨s, a, p⟩
  change (joinCylinderMap (A ⊗ P) Δ[0]).app (Opposite.op ⦋n⦌)
      (((a, p), s), PinchedHom.constant (stdSimplex.obj₀Equiv.symm 0) n) =
    (joinMap (β_ P A).hom (𝟙 Δ[0])).app (Opposite.op ⦋n⦌)
      (Join.tensorLeftSimplex P A Δ[0] n p
        ((joinCylinderMap A Δ[0]).app (Opposite.op ⦋n⦌)
          ((a, s), PinchedHom.constant (stdSimplex.obj₀Equiv.symm 0) n)))
  rw [joinCylinderMap_app, joinCylinderMap_app]
  let ℓ := ((joinStdSimplexIso.{u} 0 0).inv.app (Opposite.op ⦋n⦌) s).1
  let α := Join.prefixIncl (n + 1) ℓ.val (Nat.le_of_lt_succ ℓ.isLt)
  refine Join.Simplex.ext _ _ rfl ?_ ?_
  · change Join.augMap (A ⊗ P) α (a, p) =
      Join.augHom (β_ P A).hom ℓ.val ((Join.augTensorEquiv P A ℓ.val).symm
        (Join.augMap P α p, Join.augMap A α a))
    rw [augHom_braiding_tensor]
    exact Join.augTensorEquiv_symm_augMap A P α a p
  · let b := Join.augMap (Δ[0] : SSet.{u})
      (Join.suffixIncl (n + 1) ℓ.val (Nat.le_of_lt_succ ℓ.isLt))
      (PinchedHom.constant (stdSimplex.obj₀Equiv.symm 0) n)
    change b = Join.augHom (𝟙 (Δ[0] : SSet.{u})) (n + 1 - ℓ.val) b
    exact (Join.augHom_id Δ[0] _ b).symm

end SerrePositivity.InfinityCategories.F2
