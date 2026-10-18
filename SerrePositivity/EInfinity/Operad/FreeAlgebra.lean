module

public import SerrePositivity.EInfinity.Operad.SchurActionComposition
public import SerrePositivity.EInfinity.Operad.SchurActionUnit
public import SerrePositivity.EInfinity.Operad.SchurActionNaturality
public import SerrePositivity.EInfinity.Operad.SchurActionEquivariance

/-!
# Schur 対象上の自由オペラッド代数の構造

概要：Berger–Moerdijk §1 の Schur 対象へオペラッド代数の作用を与え、複体に関する関手を構成する。
方針：証明済みの対称性、単位作用、任意位置での部分合成則を代数のフィールドに使う。
規約：底の複体は既存の Schur 関手の対象とする。
使われ方：自由・忘却随伴の左関手として普遍性を証明する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.Operad

open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded

variable {A : Type u} [CommRing A]

/-- 概要：複体 K の Schur 対象上のオペラッド代数（Berger–Moerdijk §1）。
方針：構成した Schur 作用とその全ての代数公理を束ねる。
規約：arity 零の作用と零入力の部分合成を含む。
使われ方：自由代数関手の対象となり、普遍性の証明の始域となる。 -/
def freeAlgebra (P : Operad A) (K : Complex A) : P.Algebra where
  carrier := (schurFunctor A P.sequence).obj K
  action := P.schurAction K
  equivariance := P.schurAction_equivariance K
  unit_action := P.schurAction_unit K
  comp_action := P.schurAction_comp K

/-- 概要：複体の射から Schur 代数の射への関手（Berger–Moerdijk §1）。
方針：底の射に Schur 関手を使い、Schur 作用の自然性で代数射の保存則を証明する。
規約：対象の作用は freeAlgebra で定めたもの。
使われ方：自由・忘却随伴の左側の関手として普遍性を証明する。 -/
def freeAlgebraFunctor (P : Operad A) : Complex A ⥤ P.Algebra where
  obj := P.freeAlgebra
  map f := {
    hom := (schurFunctor A P.sequence).map f
    comm n := by
      dsimp only [freeAlgebra]
      rw [id_tensorHom]
      exact P.schurAction_naturality f n }
  map_id K := by
    apply AlgebraHom.ext
    exact (schurFunctor A P.sequence).map_id K
  map_comp f g := by
    apply AlgebraHom.ext
    exact (schurFunctor A P.sequence).map_comp f g

/-- 概要：自由代数関手の底の複体への関手は Schur 関手そのものである（Berger–Moerdijk §1）。
方針：対象と射の定義を比較する。
規約：忘却関手は既存の Algebra.forget を使う。
使われ方：自由代数の生成射と既存の Schur 関手の普遍性を同じ底の対象で使う。 -/
lemma freeAlgebraFunctor_forget (P : Operad A) :
    P.freeAlgebraFunctor ⋙ Algebra.forget P = schurFunctor A P.sequence := by
  rfl

end SerrePositivity.EInfinity.Operad
