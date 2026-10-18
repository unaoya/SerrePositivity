module

public import SerrePositivity.InfinityCategories.HomotopyLimits.FatJoinTensorRight

/-!
概要：fat join の右直積比較の自然性と通常の join の比較との整合性。
方針：円柱と左右の因子で射を比較し、円柱では区間の切断を使って計算する。
規約：比較射を選び直さず実際の射の厳密な可換性を証明する。
使われ方：Kerodon §4.6.6、7.4.1.6 の切断側の標準比較の同定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 概要：補った直積の単体を第二射影で写すと第二成分を回収する。
方針：空区間と非空区間を分け、前者は一点性、後者は直積の射影を使う。
規約：頂点数 r が零の場合も含む。
使われ方：Kerodon §4.6.6 の右直積比較と通常の join の比較の整合性。 -/
lemma augTensorEquiv_symm_augHom_snd (A B : SSet.{u}) (r : ℕ)
    (a : Join.augObj A r) (b : Join.augObj B r) :
    Join.augHom (snd A B) r ((Join.augTensorEquiv A B r).symm (a, b)) = b := by
  cases r with
  | zero => cases b; rfl
  | succ r => rfl

/-- 概要：fat join の右直積比較はパラメータの射に自然。
方針：円柱と両因子で成分の並べ替えと誘導射を計算する。
規約：全ての因子とパラメータの射は任意。
使われ方：Kerodon §4.6.6 の部分族と固定図式を保つ比較。 -/
lemma fatJoinTensorRight_parameter (A B : SSet.{u}) {P Q : SSet.{u}} (f : P ⟶ Q) :
    (fatJoin A B ◁ f) ≫ fatJoinTensorRight A B Q =
      fatJoinTensorRight A B P ≫ fatJoinMap (𝟙 A) (B ◁ f) := by
  apply fatJoin_tensorRight_hom_ext
  · have h : (fatJoinCylinder A B ▷ P) ≫ (fatJoin A B ◁ f) =
        (((A ⊗ (Δ[1] : SSet.{u})) ⊗ B) ◁ f) ≫ (fatJoinCylinder A B ▷ Q) := rfl
    rw [← Category.assoc (fatJoinCylinder A B ▷ P), h]
    simp only [Category.assoc]
    rw [fatJoinTensorRight_cylinder, ← Category.assoc (fatJoinCylinder A B ▷ P),
      fatJoinTensorRight_cylinder]
    simp only [Category.assoc]
    rw [fatJoinCylinder_map]
    rfl
  · have h : (fatJoinInl A B ▷ P) ≫ (fatJoin A B ◁ f) =
        (A ◁ f) ≫ (fatJoinInl A B ▷ Q) := rfl
    rw [← Category.assoc (fatJoinInl A B ▷ P), h]
    simp only [Category.assoc]
    rw [fatJoinTensorRight_inl, ← Category.assoc (fatJoinInl A B ▷ P),
      fatJoinTensorRight_inl]
    simp only [Category.assoc]
    rw [fatJoinInl_map, Category.id_comp]
    rfl
  · have h : (fatJoinInr A B ▷ P) ≫ (fatJoin A B ◁ f) =
        (B ◁ f) ≫ (fatJoinInr A B ▷ Q) := rfl
    rw [← Category.assoc (fatJoinInr A B ▷ P), h]
    simp only [Category.assoc]
    rw [fatJoinTensorRight_inr, ← Category.assoc (fatJoinInr A B ▷ P),
      fatJoinTensorRight_inr, fatJoinInr_map]

/-- 概要：fat join の右直積比較は通常の join の右直積比較と可換。
方針：円柱では区間を二点の join として切断位置で計算し、両端は包含の式を使う。
規約：全ての単体集合について充填性なしで成立する。
使われ方：Kerodon §4.6.6、7.4.1.6 の切断から共通模型への標準比較の整合性。 -/
lemma fatJoinTensorRight_comparison (A B P : SSet.{u}) :
    fatJoinTensorRight A B P ≫ fatJoinComparison A (B ⊗ P) =
      (fatJoinComparison A B ▷ P) ≫ joinTensorRight A B P := by
  apply fatJoin_tensorRight_hom_ext
  · rw [← Category.assoc (fatJoinCylinder A B ▷ P), fatJoinTensorRight_cylinder]
    simp only [Category.assoc, fatJoinCylinder_comparison]
    have h : (fatJoinCylinder A B ▷ P) ≫ (fatJoinComparison A B ▷ P) =
        joinCylinderMap A B ▷ P := by
      rw [← comp_whiskerRight, fatJoinCylinder_comparison]
    rw [← Category.assoc (fatJoinCylinder A B ▷ P), h]
    apply SSet.hom_ext
    rintro ⟨⟨n⟩⟩
    apply ConcreteCategory.hom_ext
    rintro ⟨⟨⟨a, t⟩, b⟩, p⟩
    change (joinMap (fst A Δ[0]) (snd Δ[0] (B ⊗ P))).app (Opposite.op ⦋n⦌)
      (Join.tensorRightSimplex (A ⊗ Δ[0]) Δ[0] (B ⊗ P) n
        (Join.tensorLeftSimplex A Δ[0] Δ[0] n a
          ((joinStdSimplexIso 0 0).inv.app (Opposite.op ⦋n⦌) t)) (b, p)) =
      Join.tensorRightSimplex A B P n
        ((joinMap (fst A Δ[0]) (snd Δ[0] B)).app (Opposite.op ⦋n⦌)
          (Join.tensorRightSimplex (A ⊗ Δ[0]) Δ[0] B n
            (Join.tensorLeftSimplex A Δ[0] Δ[0] n a
              ((joinStdSimplexIso 0 0).inv.app (Opposite.op ⦋n⦌) t)) b)) p
    generalize (joinStdSimplexIso 0 0).inv.app (Opposite.op ⦋n⦌) t = z
    rcases z with ⟨⟨l, hl⟩, z₀, z₁⟩
    cases l with
    | zero => rfl
    | succ l =>
      refine Join.Simplex.ext _ _ (by rfl) ?_ ?_
      · rfl
      · dsimp [Join.tensorRightSimplex, Join.tensorLeftSimplex, joinMap]
        rw [augTensorEquiv_symm_augHom_snd, augTensorEquiv_symm_augHom_snd]
        exact Join.augTensorEquiv_symm_augMap B P
          (r := n + 1 - (l + 1)) (s := n + 1) _ b p
  · rw [← Category.assoc (fatJoinInl A B ▷ P), fatJoinTensorRight_inl]
    simp only [Category.assoc, fatJoinInl_comparison]
    have h : (fatJoinInl A B ▷ P) ≫ (fatJoinComparison A B ▷ P) = joinInl A B ▷ P := by
      rw [← comp_whiskerRight, fatJoinInl_comparison]
    rw [← Category.assoc (fatJoinInl A B ▷ P), h, joinTensorRight_inl]
  · rw [← Category.assoc (fatJoinInr A B ▷ P), fatJoinTensorRight_inr,
      fatJoinInr_comparison]
    have h : (fatJoinInr A B ▷ P) ≫ (fatJoinComparison A B ▷ P) = joinInr A B ▷ P := by
      rw [← comp_whiskerRight, fatJoinInr_comparison]
    rw [← Category.assoc (fatJoinInr A B ▷ P), h, joinTensorRight_inr]

end SerrePositivity.InfinityCategories.HomotopyLimits
