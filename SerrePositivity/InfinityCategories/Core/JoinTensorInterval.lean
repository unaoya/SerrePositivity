module

public import SerrePositivity.InfinityCategories.Core.JoinTensorPoint
public import SerrePositivity.InfinityCategories.Core.FunctorHomotopy

/-!
概要：join の右因子の直積への比較と区間の先頭端点。
方針：第二成分が零頂点に定値であることを切断の右側へ制限して計算する。
規約：Mathlib の単体的ホモトピーの先頭包含を使う。
使われ方：Kerodon §5.3.7 の錐の頂点を固定した輸送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：補った直積の右因子の射は二成分の表示と可換。
方針：空次数は一意性、正次数は直積の定義を計算する。
規約：r は頂点数。
使われ方：Kerodon §5.3.7 の区間を含む join の自然性。 -/
lemma Join.augTensorEquiv_symm_augHomRight {C D : SSet.{u}} (A : SSet.{u}) (f : C ⟶ D)
    (r : ℕ) (a : Join.augObj A r) (c : Join.augObj C r) :
    Join.augHom (A ◁ f) r ((Join.augTensorEquiv A C r).symm (a, c)) =
      (Join.augTensorEquiv A D r).symm (a, Join.augHom f r c) := by
  cases r with
  | zero => rfl
  | succ r => rfl

/-- 概要：join の右側の直積の比較は直積パラメーターの射に自然。
方針：切断の右側の射と単体の引き戻しの自然性を使う。
規約：左右の join 因子は任意。
使われ方：Kerodon §5.3.7 の錐の輸送の区間の制限。 -/
lemma joinTensorRight_parameter {C D : SSet.{u}} (A B : SSet.{u}) (f : C ⟶ D) :
    (join A B ◁ f) ≫ joinTensorRight A B D =
      joinTensorRight A B C ≫ joinMap (𝟙 A) (B ◁ f) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨⟨ℓ, a, b⟩, c⟩
  change (⟨ℓ, a, (Join.augTensorEquiv B D (n + 1 - ℓ.val)).symm
      (b, Join.augMap D (Join.suffixIncl (n + 1) ℓ.val (Nat.le_of_lt_succ ℓ.isLt))
        (Join.augHom f (n + 1) c))⟩ : Join.Simplex A (B ⊗ D) n) =
    ⟨ℓ, Join.augHom (𝟙 A) ℓ.val a,
      Join.augHom (B ◁ f) (n + 1 - ℓ.val) ((Join.augTensorEquiv B C _).symm
        (b, Join.augMap C (Join.suffixIncl (n + 1) ℓ.val (Nat.le_of_lt_succ ℓ.isLt)) c))⟩
  refine Join.Simplex.ext _ _ rfl ?_ ?_
  · change a = Join.augHom (𝟙 A) ℓ.val a
    rw [Join.augHom_id]
  · change _ = Join.augHom (B ◁ f) (n + 1 - ℓ.val) _
    rw [Join.augTensorEquiv_symm_augHomRight, Join.augHom_naturality]
    rfl

/-- 概要：零単体から区間の先頭へ写す直積の射は先頭の端点包含を射影で前合成したもの。
方針：二つの直積成分を計算する。
規約：右因子の標準零単体を明示する。
使われ方：Kerodon §5.3.7 の区間の先頭の固定。 -/
lemma fst_stdSimplexZero_comp_ι₀ (A : SSet.{u}) :
    fst A (Δ[0] : SSet.{u}) ≫ SSet.ι₀ = A ◁ (stdSimplex.δ (1 : Fin 2)) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨a, t⟩
  apply Prod.ext
  · rfl
  · apply stdSimplex.ext
    intro i
    apply Fin.ext
    change (0 : ℕ) = ((SimplexCategory.δ (1 : Fin 2)).toOrderHom (t i)).val
    rw [Fin.eq_zero (t i)]
    rfl

/-- 概要：join と区間の右因子の直積への比較は先頭端点と可換。
方針：零単体から先頭端点への自然性と零単体の直積の射影の公式を使う。
規約：左右の join 因子は任意。
使われ方：Kerodon §5.3.7 の錐の輸送の始点の固定。 -/
lemma joinTensorRight_ι₀ (A B : SSet.{u}) :
    (SSet.ι₀ : join A B ⟶ join A B ⊗ Δ[1]) ≫ joinTensorRight A B Δ[1] =
      joinMap (𝟙 A) (SSet.ι₀ : B ⟶ B ⊗ Δ[1]) := by
  apply (cancel_epi (fst (join A B) (Δ[0] : SSet.{u}))).1
  rw [← Category.assoc, fst_stdSimplexZero_comp_ι₀, joinTensorRight_parameter,
    ← fst_stdSimplexZero_comp_ι₀ B]
  have hc : joinMap (𝟙 A) (fst B (Δ[0] : SSet.{u}) ≫ SSet.ι₀) =
      joinMap (𝟙 A) (fst B (Δ[0] : SSet.{u})) ≫ joinMap (𝟙 A) SSet.ι₀ := by
    simpa only [Category.id_comp] using
      joinMap_comp (𝟙 A) (𝟙 A) (fst B (Δ[0] : SSet.{u})) SSet.ι₀
  rw [hc, ← Category.assoc, joinTensorRight_unit]

end SerrePositivity.InfinityCategories
