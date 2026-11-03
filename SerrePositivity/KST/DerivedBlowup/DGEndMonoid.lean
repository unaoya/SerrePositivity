module

public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence
public import Mathlib.CategoryTheory.Monoidal.Mon

/-!
概要：KST §3.1 の一対象 dg 模型を複体のモノイド対象へ接続する。
方針：既存 dg 圏の自己 Hom の単位・積・圏法則を Mathlib の Mon に渡す。
規約：新しい代数公理は追加しない。
使われ方：全有限重なりの dg 代数を既存の関手型へ束ねる。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory CategoryTheory.MonoidalCategory
open DifferentialGraded

variable (R : Type u) [CommRing R]

/-- 概要：dg 圏の自己 Hom を複体のモノイド対象にする。
方針：単位律は unitor の逆での前合成を消去し、結合律は dg 圏の結合律を使う。
規約：KST §3.1。使われ方：チャート dg 代数の束ねた対象。 -/
def dgEndMonoid (D : Type v) [DGCategory R D] (x : D) : Mon (Complex R) where
  X := homObject R D x x
  mon := {
    one := eId (Complex R) x
    mul := eComp (Complex R) x x x
    one_mul := by
      apply (cancel_epi (λ_ (homObject R D x x)).inv).mp
      rw [Iso.inv_hom_id]
      exact e_id_comp (Complex R) x x
    mul_one := by
      apply (cancel_epi (ρ_ (homObject R D x x)).inv).mp
      rw [Iso.inv_hom_id]
      exact e_comp_id (Complex R) x x
    mul_assoc := (e_assoc' (Complex R) x x x x).symm }

/-- 概要：dg 関手は各自己 Hom のモノイド対象の間の射を誘導する。
方針：Hom 写像と dg 関手の単位・積保存を使う。
規約：KST §3.1。使われ方：チャート dg 遷移をモノイド対象の射にする。 -/
def dgEndMonoidMap {D : Type v} {E : Type w} [DGCategory R D] [DGCategory R E]
    (F : DGFunctor R D E) (x : D) : dgEndMonoid R D x ⟶ dgEndMonoid R E (F.obj x) :=
  Mon.Hom.mk' (F.map x x) (F.map_id x) (F.map_comp x x x)

end SerrePositivity.KST.DerivedBlowup
