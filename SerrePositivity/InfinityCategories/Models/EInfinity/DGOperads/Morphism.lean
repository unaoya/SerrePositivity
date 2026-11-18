module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Basic

/-!
模型。文献の定義との比較は後で
# 対称 dg オペラッドの射

概要：Berger–Moerdijk §1 のオペラッド射を既存の対称列の自然変換で定義する。
方針：単位と各部分合成の保存則を課し、恒等射と合成を構成する。
規約：対称群作用との両立は自然変換の自然性に含まれる。
使われ方：Barratt–Eccles の augmentation と、演算の係数の移送に用いる。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded

namespace Operad

variable {A : Type u} [CommRing A]

/-- 概要：単位と部分合成を保つ対称 dg オペラッドの射（Berger–Moerdijk §1）。
方針：既存の対称列の自然変換に保存則を課す。
規約：arity 0 の部分合成も保つ。
使われ方：E → Com の augmentation の型を与える。 -/
@[ext]
structure Hom (P Q : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) where
  /-- 概要：対称列の間の自然変換（Berger–Moerdijk §1）。
  方針：各 arity の chain map を置換と両立させて束ねる。
  規約：対称列の既存の圏の射をそのまま使う。
  使われ方：オペラッド射の各 arity の成分となる。 -/
  map : P.sequence ⟶ Q.sequence
  /-- 概要：単位演算の保存則（Berger–Moerdijk §1）。
  方針：単位の chain map の後に arity 1 の成分を合成する。
  規約：テンソル単位は底の複体圏のもの。
  使われ方：単位的な代数構造を係数とともに移送する。 -/
  unit : P.unit ≫ map.app (_root_.SerrePositivity.FiniteBijection.of 1) = Q.unit
  /-- 概要：全ての部分合成の保存則（Berger–Moerdijk §1）。
  方針：合成後の成分と、両因子の成分を合成前に適用した結果を比較する。
  規約：全入力位置と arity 0 の代入を含む。
  使われ方：オペラッドの代数を係数の射に沿って移送する。 -/
  comp (m n : ℕ) (i : Fin (m + 1)) :
    P.comp m n i ≫ map.app (_root_.SerrePositivity.FiniteBijection.of (m + n)) =
      (map.app (_root_.SerrePositivity.FiniteBijection.of (m + 1)) ⊗ₘ map.app (_root_.SerrePositivity.FiniteBijection.of n)) ≫ Q.comp m n i

/-- 概要：対称 dg オペラッドは圏をなす（Berger–Moerdijk §1）。
方針：底の自然変換の恒等射・合成とテンソル射の合成則を使う。
規約：異なるモデル構造の選択を必要としない。
使われ方：augmentation やオペラッドの比較射を合成する。 -/
instance _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.instCategory : Category (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) where
  Hom := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hom
  id P := {
    map := 𝟙 P.sequence
    unit := by
      change P.unit ≫ 𝟙 (P.arity 1) = P.unit
      exact Category.comp_id _
    comp m n i := by
      change P.comp m n i ≫ 𝟙 (P.arity (m + n)) =
        (𝟙 (P.arity (m + 1)) ⊗ₘ 𝟙 (P.arity n)) ≫ P.comp m n i
      rw [Category.comp_id, tensorHom_id, id_whiskerRight, Category.id_comp] }
  comp f g := {
    map := f.map ≫ g.map
    unit := by rw [NatTrans.comp_app, ← Category.assoc, f.unit, g.unit]
    comp m n i := by
      rw [NatTrans.comp_app, ← Category.assoc, f.comp, Category.assoc, g.comp]
      simp only [← Category.assoc, tensorHom_comp_tensorHom]
      rfl }
  id_comp f := by apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hom.ext; exact Category.id_comp f.map
  comp_id f := by apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hom.ext; exact Category.comp_id f.map
  assoc f g h := by apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hom.ext; exact Category.assoc f.map g.map h.map

/-- 概要：オペラッドから底の対称列への忘却関手（Berger–Moerdijk §1）。
方針：対象を sequence、射を map に送る。
規約：代数から複体への忘却関手と区別する。
使われ方：オペラッド射を各 arity の chain map で計算する。 -/
def toSymmetricSequence : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A ⥤ _root_.SerrePositivity.SymmetricSequence (Complex A) where
  obj P := P.sequence
  map f := f.map

/-- 概要：対称列への忘却関手は忠実（Berger–Moerdijk §1）。
方針：オペラッド射は自然変換と保存則の証明からなる。
規約：保存則を射の余分なデータと区別する。
使われ方：オペラッド射の等式を自然変換の等式で判定する。 -/
instance toSymmetricSequence_faithful : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.toSymmetricSequence (A := A)).Faithful where
  map_injective h := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hom.ext h

end Operad

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
