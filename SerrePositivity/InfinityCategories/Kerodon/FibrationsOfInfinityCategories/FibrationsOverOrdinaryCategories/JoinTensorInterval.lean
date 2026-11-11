module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinTensorPoint
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorHomotopy

/-!
概要：join の右因子の直積への比較と区間の先頭端点。
方針：第二成分が零頂点に定値であることを切断の右側へ制限して計算する。
規約：Mathlib の単体的ホモトピーの先頭包含を使う。
使われ方：Kerodon §5.3.7（Tag 01US） の錐の頂点を固定した輸送。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 概要：補った直積の右因子の射は二成分の表示と可換。
方針：空次数は一意性、正次数は直積の定義を計算する。
規約：r は頂点数。
使われ方：Kerodon §5.3.7（Tag 01US） の区間を含む join の自然性。 -/
lemma Join.augTensorEquiv_symm_augHomRight {C D : SSet.{u}} (A : SSet.{u}) (f : C ⟶ D)
    (r : ℕ) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj A r) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj C r) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom (A ◁ f) r ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Join.augTensorEquiv A C r).symm (a, c)) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Join.augTensorEquiv A D r).symm (a, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom f r c) := by
  cases r with
  | zero => rfl
  | succ r => rfl

/-- 概要：join の右側の直積の比較は直積パラメーターの射に自然。
方針：切断の右側の射と単体の引き戻しの自然性を使う。
規約：左右の join 因子は任意。
使われ方：Kerodon §5.3.7（Tag 01US） の錐の輸送の区間の制限。 -/
lemma joinTensorRight_parameter {C D : SSet.{u}} (A B : SSet.{u}) (f : C ⟶ D) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A B ◁ f) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinTensorRight A B D =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinTensorRight A B C ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 A) (B ◁ f) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨⟨ℓ, a, b⟩, c⟩
  change (⟨ℓ, a, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Join.augTensorEquiv B D (n + 1 - ℓ.val)).symm
      (b, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap D (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Join.suffixIncl (n + 1) ℓ.val (Nat.le_of_lt_succ ℓ.isLt))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom f (n + 1) c))⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex A (B ⊗ D) n) =
    ⟨ℓ, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom (𝟙 A) ℓ.val a,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom (B ◁ f) (n + 1 - ℓ.val) ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Join.augTensorEquiv B C _).symm
        (b, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap C (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Join.suffixIncl (n + 1) ℓ.val (Nat.le_of_lt_succ ℓ.isLt)) c))⟩
  refine _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex.ext _ _ rfl ?_ ?_
  · change a = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom (𝟙 A) ℓ.val a
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom_id]
  · change _ = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom (B ◁ f) (n + 1 - ℓ.val) _
    rw [Join.augTensorEquiv_symm_augHomRight, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom_naturality]
    rfl

/-- 概要：零単体から区間の先頭へ写す直積の射は先頭の端点包含を射影で前合成したもの。
方針：二つの直積成分を計算する。
規約：右因子の標準零単体を明示する。
使われ方：Kerodon §5.3.7（Tag 01US） の区間の先頭の固定。 -/
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
使われ方：Kerodon §5.3.7（Tag 01US） の錐の輸送の始点の固定。 -/
lemma joinTensorRight_ι₀ (A B : SSet.{u}) :
    (SSet.ι₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A B ⊗ Δ[1]) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinTensorRight A B Δ[1] =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 A) (SSet.ι₀ : B ⟶ B ⊗ Δ[1]) := by
  apply (cancel_epi (fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A B) (Δ[0] : SSet.{u}))).1
  rw [← Category.assoc, fst_stdSimplexZero_comp_ι₀, joinTensorRight_parameter,
    ← fst_stdSimplexZero_comp_ι₀ B]
  have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 A) (fst B (Δ[0] : SSet.{u}) ≫ SSet.ι₀) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 A) (fst B (Δ[0] : SSet.{u})) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 A) SSet.ι₀ := by
    simpa only [Category.id_comp] using
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp (𝟙 A) (𝟙 A) (fst B (Δ[0] : SSet.{u})) SSet.ι₀
  rw [hc, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinTensorRight_unit]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
