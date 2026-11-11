module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CubeBlockIndices
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CubeEvaluation
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# 二つの座標集合を順に並べた最大旗

概要：二つの番号付けを連結し、その旗の左右への射影を接頭・接尾で元の旗に戻す。
方針：Fin の和の同値を使い、逆番号付けの値を左右で計算する。
規約：後の射の座標を先頭、前の射の座標を末尾に並べる。
使われ方：HA 1.3.1.16、Kerodon 2.5.8（Tag 00S0） の AW と shuffle の唯一の非退化項。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory
open scoped _root_.Simplicial

/-- 概要：二つの座標の番号付けを順に連結する。
方針：Fin(p+q) を Fin p と Fin q の和に分ける。
規約：先頭 p 座標が左の和、末尾 q 座標が右の和。
使われ方：Kerodon 2.5.8（Tag 00S0） の AW の境目に適合した旗の番号付け。 -/
def cubeSumEnumeration {A B : Type u} {p q : ℕ} (e : Fin p ≃ A) (f : Fin q ≃ B) :
    Fin (p + q) ≃ A ⊕ B := finSumFinEquiv.symm.trans (Equiv.sumCongr e f)

/-- 概要：和の立方体を左の座標集合へ射影する。
方針：左の包含による部分集合の逆像の nerve を取る。
規約：右の座標は忘れる。
使われ方：HA 1.3.1.16 の後の射への座標射影。 -/
def cubeSumLeftMap (A B : Type u) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube (A ⊕ B) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube A :=
  nerveMap (show Monotone (fun U : Set (A ⊕ B) ↦ Sum.inl ⁻¹' U) from
    fun _ _ h _ ha ↦ h ha).functor

/-- 概要：和の立方体を右の座標集合へ射影する。
方針：右の包含による部分集合の逆像の nerve を取る。
規約：左の座標は忘れる。
使われ方：HA 1.3.1.16 の前の射への座標射影。 -/
def cubeSumRightMap (A B : Type u) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube (A ⊕ B) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube B :=
  nerveMap (show Monotone (fun U : Set (A ⊕ B) ↦ Sum.inr ⁻¹' U) from
    fun _ _ h _ ha ↦ h ha).functor

/-- 概要：連結した番号付けの左座標の逆番号は先頭区間の番号である。
方針：和の同値の左側の計算を使う。
規約：番号の値は変わらない。
使われ方：Kerodon 2.5.8（Tag 00S0） の接頭の旗の計算。 -/
lemma cubeSumEnumeration_symm_inl {A B : Type u} {p q : ℕ}
    (e : Fin p ≃ A) (f : Fin q ≃ B) (a : A) :
    (cubeSumEnumeration e f).symm (Sum.inl a) = Fin.castAdd q (e.symm a) := by
  simp [cubeSumEnumeration]

/-- 概要：連結した番号付けの右座標の逆番号は p だけ移動した番号である。
方針：和の同値の右側の計算を使う。
規約：先頭の座標数 p を加える。
使われ方：Kerodon 2.5.8（Tag 00S0） の接尾の旗の計算。 -/
lemma cubeSumEnumeration_symm_inr {A B : Type u} {p q : ℕ}
    (e : Fin p ≃ A) (f : Fin q ≃ B) (b : B) :
    (cubeSumEnumeration e f).symm (Sum.inr b) = Fin.natAdd p (f.symm b) := by
  simp [cubeSumEnumeration]

/-- 概要：連結した旗の左射影の接頭は元の左の最大旗に等しい。
方針：左座標の逆番号と接頭頂点の番号はともに移動しない。
規約：単体の引き戻しは頂点包含の反対射で表す。
使われ方：HA 1.3.1.16 の AW の後の射の最上位評価。 -/
lemma cubeSumLeftMap_flag_prefix {A B : Type u} {p q : ℕ}
    (e : Fin p ≃ A) (f : Fin q ≃ B) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube A).map (SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubePrefixOrder p q)).op
      ((cubeSumLeftMap A B).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag (cubeSumEnumeration e f))) = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag e := by
  refine CategoryTheory.Functor.ext (fun t ↦ ?_)
  apply Set.ext
  intro a
  change ((cubeSumEnumeration e f).symm (Sum.inl a)).val < (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubePrefixOrder p q t).val ↔
    (e.symm a).val < t.val
  rw [cubeSumEnumeration_symm_inl]
  rfl

/-- 概要：連結した旗の右射影の接尾は元の右の最大旗に等しい。
方針：逆番号と頂点番号の両方から先頭座標数 p を消す。
規約：左右の共通の境目の頂点を右の零頂点へ移す。
使われ方：HA 1.3.1.16 の AW の前の射の最上位評価。 -/
lemma cubeSumRightMap_flag_suffix {A B : Type u} {p q : ℕ}
    (e : Fin p ≃ A) (f : Fin q ≃ B) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube B).map (SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeSuffixOrder p q)).op
      ((cubeSumRightMap A B).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag (cubeSumEnumeration e f))) = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag f := by
  refine CategoryTheory.Functor.ext (fun t ↦ ?_)
  apply Set.ext
  intro b
  change ((cubeSumEnumeration e f).symm (Sum.inr b)).val < (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeSuffixOrder p q t).val ↔
    (f.symm b).val < t.val
  rw [cubeSumEnumeration_symm_inr]
  change p + (f.symm b).val < p + t.val ↔ (f.symm b).val < t.val
  omega

/-- 概要：左射影の旗では右座標が加わる前後の頂点が一致する。
方針：全ての左座標はその時点より前に加わっている。
規約：右座標 r の全体での番号は p+r。
使われ方：Kerodon 2.5.8（Tag 00S0） の境目より後の AW 切断項の消去。 -/
lemma cubeSumLeftMap_flag_repeat_right {A B : Type u} {p q : ℕ}
    (e : Fin p ≃ A) (f : Fin q ≃ B) (r : Fin q) :
    ((cubeSumLeftMap A B).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag (cubeSumEnumeration e f))).obj
        (Fin.natAdd p r).castSucc =
      ((cubeSumLeftMap A B).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag (cubeSumEnumeration e f))).obj
        (Fin.natAdd p r).succ := by
  apply Set.ext
  intro a
  change ((cubeSumEnumeration e f).symm (Sum.inl a)).val < p + r.val ↔
    ((cubeSumEnumeration e f).symm (Sum.inl a)).val < p + r.val + 1
  rw [cubeSumEnumeration_symm_inl]
  change (e.symm a).val < p + r.val ↔ (e.symm a).val < p + r.val + 1
  have h := (e.symm a).isLt
  omega

/-- 概要：右射影の旗では左座標が加わる前後の頂点が一致する。
方針：右座標はその時点ではまだ一つも加わっていない。
規約：左座標 r の全体での番号は r。
使われ方：Kerodon 2.5.8（Tag 00S0） の境目より前の AW 切断項の消去。 -/
lemma cubeSumRightMap_flag_repeat_left {A B : Type u} {p q : ℕ}
    (e : Fin p ≃ A) (f : Fin q ≃ B) (r : Fin p) :
    ((cubeSumRightMap A B).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag (cubeSumEnumeration e f))).obj
        (Fin.castAdd q r).castSucc =
      ((cubeSumRightMap A B).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag (cubeSumEnumeration e f))).obj
        (Fin.castAdd q r).succ := by
  apply Set.ext
  intro b
  change ((cubeSumEnumeration e f).symm (Sum.inr b)).val < r.val ↔
    ((cubeSumEnumeration e f).symm (Sum.inr b)).val < r.val + 1
  rw [cubeSumEnumeration_symm_inr]
  change p + (f.symm b).val < r.val ↔ p + (f.symm b).val < r.val + 1
  have h := r.isLt
  omega

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
