module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.InitialNerveTail

/-!
概要：空単体を補った nerve の対象と射を、存在する頂点で評価する。
方針：頂点数が零の場合を空の添字で除き、正の場合は射列を評価する。
規約：空単体から対象を選ばず、順序写像に沿う再添字付けを明示する。
使われ方：HTT 1.2.8、Kerodon 4.3.5（Tag 017V） の点と nerve の join の比較。

対応節は Kerodon 4.3（Tag 015M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
variable {C : Type u} [SmallCategory C]

/-- 概要：空単体を補った nerve の単体を指定した頂点で評価する。
方針：頂点数が正なら射列の対象を取り、零なら空の添字を除く。
規約：元の圏の非空性は要求しない。
使われ方：HTT 1.2.8、Kerodon 4.3.5（Tag 017V） の join の後半の頂点。 -/
def augNerveObj : {r : ℕ} → _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj (nerve C) r → Fin r → C
  | 0, _, i => Fin.elim0 i
  | _ + 1, τ, i => τ.obj i

/-- 概要：補った nerve の単体を頂点の大小関係に対応する射で評価する。
方針：頂点数が正なら射列の射を取り、零なら空の添字を除く。
規約：端点は augNerveObj により評価する。
使われ方：HTT 1.2.8、Kerodon 4.3.5（Tag 017V） の join の後半の射。 -/
def augNerveMap : {r : ℕ} → (τ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj (nerve C) r) →
    {i j : Fin r} → i ≤ j → (augNerveObj τ i ⟶ augNerveObj τ j)
  | 0, _, i, _, _ => Fin.elim0 i
  | _ + 1, τ, _, _, h => τ.map (homOfLE h)

/-- 概要：同じ頂点の評価は恒等射である。
方針：空の添字を除き、射列の恒等射の保存を使う。
規約：大小関係の証明は反射律を使う。
使われ方：HTT 1.2.8、Kerodon 4.3.5（Tag 017V） の join の射列の関手法則。 -/
lemma augNerveMap_id {r : ℕ} (τ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj (nerve C) r) (i : Fin r) :
    augNerveMap τ (le_refl i) = 𝟙 (augNerveObj τ i) := by
  cases r with
  | zero => exact Fin.elim0 i
  | succ r => exact τ.map_id i

/-- 概要：補った nerve の射の評価は合成を保つ。
方針：空の添字を除き、射列の合成の保存を使う。
規約：合成は小さい頂点から大きい頂点へ進む。
使われ方：HTT 1.2.8、Kerodon 4.3.5（Tag 017V） の join の射列の関手法則。 -/
lemma augNerveMap_comp {r : ℕ} (τ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj (nerve C) r)
    {i j k : Fin r} (hij : i ≤ j) (hjk : j ≤ k) :
    augNerveMap τ (hij.trans hjk) = augNerveMap τ hij ≫ augNerveMap τ hjk := by
  cases r with
  | zero => exact Fin.elim0 i
  | succ r => exact τ.map_comp (homOfLE hij) (homOfLE hjk)

/-- 概要：順序写像による引き戻しの頂点は写した添字での元の頂点に等しい。
方針：空の場合を除き、nerve の再添字付けの定義を読む。
規約：始域が空なら評価する頂点も存在しない。
使われ方：HTT 1.2.8、Kerodon 4.3.5（Tag 017V） の join の単体的自然性。 -/
lemma augNerveObj_augMap {m r : ℕ} (α : Fin m →o Fin r)
    (τ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj (nerve C) r) (i : Fin m) :
    augNerveObj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap (nerve C) α τ) i = augNerveObj τ (α i) := by
  cases m with
  | zero => exact Fin.elim0 i
  | succ m =>
    cases r with
    | zero => exact Fin.elim0 (α i)
    | succ r => rfl

/-- 概要：順序写像による引き戻しの射は元の単体の対応する射に移送で一致する。
方針：空の場合を除き、nerve の再添字付けの定義を読む。
規約：端点の等式は augNerveObj_augMap を使う。
使われ方：HTT 1.2.8、Kerodon 4.3.5（Tag 017V） の join の単体的自然性。 -/
lemma augNerveMap_augMap {m r : ℕ} (α : Fin m →o Fin r)
    (τ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj (nerve C) r) {i j : Fin m} (h : i ≤ j) :
    augNerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap (nerve C) α τ) h ≫
        eqToHom (augNerveObj_augMap α τ j) =
      eqToHom (augNerveObj_augMap α τ i) ≫ augNerveMap τ (α.monotone h) := by
  cases m with
  | zero => exact Fin.elim0 i
  | succ m =>
    cases r with
    | zero => exact Fin.elim0 (α i)
    | succ r =>
      simp only [augNerveMap, eqToHom_refl, Category.comp_id, Category.id_comp]
      rfl

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
