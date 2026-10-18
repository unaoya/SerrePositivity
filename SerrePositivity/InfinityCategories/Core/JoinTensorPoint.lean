module

public import SerrePositivity.InfinityCategories.Core.FatJoinFunctor

/-!
概要：標準零単体を直積の因子とする join の比較の同型性。
方針：零単体の終対象性と join の同型への関手性を使う。
規約：標準零単体とモノイダル単位の同型を明示する。
使われ方：Kerodon §4.6.2 の標準単体の fat join の基本例。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：標準零単体とモノイダル単位の標準同型。
方針：二つの終対象の一意な同型を取る。
規約：Mathlib のモノイダル単位を標準零単体と定義的に同一視しない。
使われ方：Kerodon §4.6.2 の点を直積因子とする比較。 -/
def stdSimplexZeroUnitIso : (Δ[0] : SSet.{u}) ≅ 𝟙_ SSet.{u} :=
  stdSimplex.isTerminalObj₀.uniqueUpToIso isTerminalTensorUnit

/-- 概要：標準零単体への単位射は同型。
方針：終対象間の標準同型と一致することを使う。
規約：対象は標準零単体からモノイダル単位への射。
使われ方：Kerodon §4.6.2 の直積の射影。 -/
instance isIso_toUnit_stdSimplexZero : IsIso (toUnit (Δ[0] : SSet.{u})) := by
  have h : toUnit (Δ[0] : SSet.{u}) = stdSimplexZeroUnitIso.hom :=
    isTerminalTensorUnit.hom_ext _ _
  rw [h]
  infer_instance

/-- 概要：標準零単体を右因子に持つ直積の第一射影は同型。
方針：単位への同型と右単位子で表示する。
規約：第一因子は任意。
使われ方：Kerodon §4.6.2 の点の円柱。 -/
instance isIso_fst_stdSimplexZero (A : SSet.{u}) : IsIso (fst A (Δ[0] : SSet.{u})) := by
  have : IsIso (isTerminalTensorUnit.from (Δ[0] : SSet.{u})) :=
    isIso_toUnit_stdSimplexZero
  rw [fst_def]
  infer_instance

/-- 概要：標準零単体を左因子に持つ直積の第二射影は同型。
方針：単位への同型と左単位子で表示する。
規約：第二因子は任意。
使われ方：Kerodon §4.6.2 の点の円柱。 -/
instance isIso_snd_stdSimplexZero (A : SSet.{u}) : IsIso (snd (Δ[0] : SSet.{u}) A) := by
  have : IsIso (isTerminalTensorUnit.from (Δ[0] : SSet.{u})) :=
    isIso_toUnit_stdSimplexZero
  rw [snd_def]
  infer_instance

/-- 概要：二つの同型は join の同型を誘導する。
方針：joinMap の恒等射と合成の法則を使う。
規約：任意の単体集合の同型。
使われ方：Kerodon §4.3.5、§4.6.2 の模型の比較。 -/
def joinIso {A A' B B' : SSet.{u}} (e : A ≅ A') (f : B ≅ B') : join A B ≅ join A' B' where
  hom := joinMap e.hom f.hom
  inv := joinMap e.inv f.inv
  hom_inv_id := by rw [← joinMap_comp, e.hom_inv_id, f.hom_inv_id, joinMap_id]
  inv_hom_id := by rw [← joinMap_comp, e.inv_hom_id, f.inv_hom_id, joinMap_id]

/-- 概要：同型な二つの射の join への誘導射は同型。
方針：明示的な join の同型を用いる。
規約：元の対象の quasicategory 性は不要。
使われ方：Kerodon §4.6.2 の円柱の同型性。 -/
instance isIso_joinMap {A A' B B' : SSet.{u}} (f : A ⟶ A') (g : B ⟶ B')
    [IsIso f] [IsIso g] : IsIso (joinMap f g) := (joinIso (asIso f) (asIso g)).isIso_hom

/-- 概要：補った直積の単体から第一成分を射影すると元の第一単体になる。
方針：空次数は一意性、非空次数は直積の計算を使う。
規約：r は頂点数。
使われ方：Kerodon §4.6.2 の join と直積の比較。 -/
lemma Join.augTensorEquiv_symm_augHomFst (A B : SSet.{u}) (r : ℕ)
    (a : Join.augObj A r) (b : Join.augObj B r) :
    Join.augHom (fst A B) r ((Join.augTensorEquiv A B r).symm (a, b)) = a := by
  cases r with
  | zero => cases a; rfl
  | succ r => rfl

/-- 概要：右側の直積の比較は標準零単体の成分を射影すると元の join に戻る。
方針：切断の両側で直積の第一成分を計算する。
規約：左と右の join 因子は任意。
使われ方：Kerodon §4.6.2 の点の円柱の比較。 -/
lemma joinTensorRight_unit (A B : SSet.{u}) :
    joinTensorRight A B (Δ[0] : SSet.{u}) ≫ joinMap (𝟙 A) (fst B (Δ[0] : SSet.{u})) =
      fst (join A B) (Δ[0] : SSet.{u}) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨⟨ℓ, a, b⟩, c⟩
  change (⟨ℓ, Join.augHom (𝟙 A) ℓ.val a,
    Join.augHom (fst B (Δ[0] : SSet.{u})) (n + 1 - ℓ.val)
      ((Join.augTensorEquiv B (Δ[0] : SSet.{u}) _).symm
        (b, Join.augMap (Δ[0] : SSet.{u}) (Join.suffixIncl _ _ _) c))⟩ : Join.Simplex A B n) =
    ⟨ℓ, a, b⟩
  rw [Join.augHom_id, Join.augTensorEquiv_symm_augHomFst]

/-- 概要：直積の第一因子が標準零単体なら左側の join 比較は同型。
方針：零単体を射影した後の等式と同型の消去を使う。
規約：join の二因子は任意。
使われ方：Kerodon §4.6.2 の基本の比較。 -/
instance isIso_joinTensorLeft_point (B C : SSet.{u}) :
    IsIso (joinTensorLeft (Δ[0] : SSet.{u}) B C) :=
  IsIso.of_isIso_fac_right (joinTensorLeft_unit B C)

/-- 概要：直積の第二因子が標準零単体なら右側の join 比較は同型。
方針：零単体を射影した後の等式と同型の消去を使う。
規約：join の二因子は任意。
使われ方：Kerodon §4.6.2 の基本の比較。 -/
instance isIso_joinTensorRight_point (A B : SSet.{u}) :
    IsIso (joinTensorRight A B (Δ[0] : SSet.{u})) :=
  IsIso.of_isIso_fac_right (joinTensorRight_unit A B)

end SerrePositivity.InfinityCategories
