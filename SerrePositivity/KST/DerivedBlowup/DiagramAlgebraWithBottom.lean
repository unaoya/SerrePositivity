module

public import SerrePositivity.KST.DerivedBlowup.DiagramAlgebraVertex
public import Mathlib.Order.WithBot

/-!
概要：KST §3.1 の局所自由図式加群を作るための補助始点の追加。
方針：dg 代数図式に単位 dg 代数を持つ最小頂点を付け加える。
規約：元の全図式係数圏は保持し、補助頂点の共変 representable を制限して使う。
使われ方：構造加群と捻り加群の大域図式での実現。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory
open DifferentialGraded

variable {R : Type u} [CommRing R] {J : Type v} [Preorder J]
variable (F : J ⥤ Mon (Complex R))

/-- 概要：補助始点では単位 dg 代数、元の頂点では元の係数を使う。
方針：WithBot の二つの場合で定義する。
規約：KST §3.1。使われ方：補助係数関手の対象。 -/
def diagramAlgebraWithBottomObj : WithBot J → Mon (Complex R)
  | none => Mon.trivial (Complex R)
  | some i => F.obj i

/-- 概要：補助始点からの射は dg 代数の単位、元の射は元の図式の射。
方針：単位 dg 代数からの一意なモノイド対象の射を使う。
規約：KST §3.1。使われ方：補助係数関手の射。 -/
def diagramAlgebraWithBottomMap {i j : WithBot J} (h : i ≤ j) :
    diagramAlgebraWithBottomObj F i ⟶ diagramAlgebraWithBottomObj F j :=
  match i, j with
  | none, j => (default : Mon.trivial (Complex R) ⟶ diagramAlgebraWithBottomObj F j)
  | some i, none => False.elim (WithBot.not_coe_le_bot i h)
  | some _, some _ => F.map (homOfLE (WithBot.coe_le_coe.mp h))

/-- 概要：単位 dg 代数を持つ補助最小頂点を加えた係数図式。
方針：元の関手法則と単位 dg 代数からの射の一意性を使う。
規約：KST §3.1、元の図式を補助頂点へ置き換えるものではない。
使われ方：補助頂点の representable から元の構造加群を構成する。 -/
def diagramAlgebraWithBottom : WithBot J ⥤ Mon (Complex R) where
  obj := diagramAlgebraWithBottomObj F
  map f := diagramAlgebraWithBottomMap F (leOfHom f)
  map_id i := by
    cases i with
    | bot =>
      change @Eq (Mon.trivial (Complex R) ⟶ Mon.trivial (Complex R)) _ _
      exact Subsingleton.elim _ _
    | coe i => exact F.map_id i
  map_comp {i j k} f g := by
    cases i with
    | bot =>
      change @Eq (Mon.trivial (Complex R) ⟶ diagramAlgebraWithBottomObj F k) _ _
      exact Subsingleton.elim _ _
    | coe i =>
      cases j with
      | bot => exact False.elim (WithBot.not_coe_le_bot i (leOfHom f))
      | coe j =>
        cases k with
        | bot => exact False.elim (WithBot.not_coe_le_bot j (leOfHom g))
        | coe k =>
          exact F.map_comp (homOfLE (WithBot.coe_le_coe.mp (leOfHom f)))
            (homOfLE (WithBot.coe_le_coe.mp (leOfHom g)))

end SerrePositivity.KST.DerivedBlowup
