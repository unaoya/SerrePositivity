module

public import SerrePositivity.InfinityCategories.Core.FatJoinTensorExt
public import SerrePositivity.InfinityCategories.Core.FatJoinComparison

/-!
概要：fat join と直積の比較は通常の join との比較に整合する。
方針：円柱と両因子上で、同じ切断への直積成分の制限を比較する。
規約：全ての単体集合は任意。
使われ方：Kerodon §4.6.6 の二つの slice 比較射の同定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：fat join と直積の比較は通常の join との比較射と可換。
方針：円柱と両因子上で計算し、円柱では区間が指定する切断で分ける。
規約：P、A、K の quasicategory 性・非空性は不要。
使われ方：Kerodon §4.6.6 の太い slice と関手の錐の比較の整合性。 -/
lemma fatJoinTensorLeft_comparison (P A K : SSet.{u}) :
    fatJoinTensorLeft P A K ≫ fatJoinComparison (P ⊗ A) K =
      (P ◁ fatJoinComparison A K) ≫ joinTensorLeft P A K := by
  apply fatJoin_tensorLeft_hom_ext
  · have hs : (P ◁ fatJoinCylinder A K) ≫ (P ◁ fatJoinComparison A K) =
        P ◁ joinCylinderMap A K := by rw [← whiskerLeft_comp, fatJoinCylinder_comparison]
    rw [← Category.assoc (P ◁ fatJoinCylinder A K), fatJoinTensorLeft_cylinder]
    simp only [Category.assoc, fatJoinCylinder_comparison]
    rw [← Category.assoc (P ◁ fatJoinCylinder A K), hs]
    apply SSet.hom_ext
    rintro ⟨⟨n⟩⟩
    apply ConcreteCategory.hom_ext
    rintro ⟨p, ⟨⟨a, t⟩, k⟩⟩
    change (joinMap (fst (P ⊗ A) Δ[0]) (snd Δ[0] K)).app (Opposite.op ⦋n⦌)
      (Join.tensorRightSimplex ((P ⊗ A) ⊗ Δ[0]) Δ[0] K n
        (Join.tensorLeftSimplex (P ⊗ A) Δ[0] Δ[0] n (p, a)
          ((joinStdSimplexIso 0 0).inv.app (Opposite.op ⦋n⦌) t)) k) =
      Join.tensorLeftSimplex P A K n p
        ((joinMap (fst A Δ[0]) (snd Δ[0] K)).app (Opposite.op ⦋n⦌)
          (Join.tensorRightSimplex (A ⊗ Δ[0]) Δ[0] K n
            (Join.tensorLeftSimplex A Δ[0] Δ[0] n a
              ((joinStdSimplexIso 0 0).inv.app (Opposite.op ⦋n⦌) t)) k))
    generalize (joinStdSimplexIso 0 0).inv.app (Opposite.op ⦋n⦌) t = z
    rcases z with ⟨⟨l, hl⟩, z₀, z₁⟩
    cases l with
    | zero => rfl
    | succ l => rfl

  · rw [← Category.assoc (P ◁ fatJoinInl A K), fatJoinTensorLeft_inl, fatJoinInl_comparison]
    have hs : (P ◁ fatJoinInl A K) ≫ (P ◁ fatJoinComparison A K) = P ◁ joinInl A K := by
      rw [← whiskerLeft_comp, fatJoinInl_comparison]
    rw [← Category.assoc, hs, joinTensorLeft_inl]
  · rw [← Category.assoc (P ◁ fatJoinInr A K), fatJoinTensorLeft_inr]
    simp only [Category.assoc, fatJoinInr_comparison]
    have hs : (P ◁ fatJoinInr A K) ≫ (P ◁ fatJoinComparison A K) = P ◁ joinInr A K := by
      rw [← whiskerLeft_comp, fatJoinInr_comparison]
    rw [← Category.assoc, hs, joinTensorLeft_inr]

end SerrePositivity.InfinityCategories
