module

public import Mathlib.CategoryTheory.Limits.Shapes.End
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Whiskering

/-!
概要：右随伴関手と end の交換同型。
方針：射影を右随伴に送り、逆射は随伴の Hom 同値で end への持ち上げに戻す。
規約：二つの end の存在を明示する。
使われ方：HA §1.4.2、BF 1978 §2。pointed end の忘却と Kan 模型との比較。
-/

@[expose] public section

universe u v w z a b

open CategoryTheory Limits Opposite

namespace SerrePositivity.KST.Spectra.EndRightAdjoint

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {C : Type u} [Category.{v} C] {E : Type w} [Category.{z} E]
  {J : Type a} [Category.{b} J] {L : C ⥤ E} {R : E ⥤ C}

/-- 概要：二変数の end の図式を右随伴関手で後合成する。
方針：内側の図式への後合成を外側にも適用する。
規約：始域と終域の圏は異なってよい。
使われ方：HA §1.4.2。忘却後の end の図式。 -/
def postDiagram (R : E ⥤ C) (D : Jᵒᵖ ⥤ J ⥤ E) : Jᵒᵖ ⥤ J ⥤ C :=
  D ⋙ (Functor.whiskeringRight J E C).obj R

variable (adj : L ⊣ R) (D : Jᵒᵖ ⥤ J ⥤ E)
  [HasEnd D] [HasEnd (postDiagram R D)]

/-- 概要：右随伴を施した end から後合成した図式の end への比較。
方針：元の end の射影に右随伴を施す。
規約：随伴を含めない方向の射。
使われ方：HA §1.4.2。pointed end を忘れた後の比較。 -/
def toEnd : R.obj (end_ D) ⟶ end_ (postDiagram R D) :=
  end_.lift (fun j ↦ R.map (end_.π D j)) (fun i j f ↦ by
    change R.map (end_.π D i) ≫ R.map ((D.obj (op i)).map f) =
      R.map (end_.π D j) ≫ R.map ((D.map f.op).app j)
    rw [← Functor.map_comp, ← Functor.map_comp, end_.condition D f])

/-- 概要：後合成した図式の end から右随伴を施した end への逆比較。
方針：射影を随伴で元の圏へ戻し、end へ持ち上げた後で再び随伴を適用する。
規約：右随伴の一意性だけで存在を仮定しない実際の射。
使われ方：HA §1.4.2。二つの end の同型の構成。 -/
def fromEnd : end_ (postDiagram R D) ⟶ R.obj (end_ D) :=
  adj.homEquiv _ _ (end_.lift
    (fun j ↦ (adj.homEquiv _ _).symm (end_.π (postDiagram R D) j)) (fun i j f ↦ by
      apply (adj.homEquiv _ _).injective
      rw [adj.homEquiv_naturality_right, adj.homEquiv_naturality_right,
        Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      exact end_.condition (postDiagram R D) f))

/-- 概要：順比較の射影は元の射影への右随伴の作用。
方針：end の持ち上げの成分式を使う。
規約：厳密な等式。
使われ方：HA §1.4.2。end の交換の計算。 -/
@[reassoc (attr := simp)]
theorem toEnd_π (j : J) : toEnd (R := R) D ≫ end_.π (postDiagram R D) j =
    R.map (end_.π D j) := end_.lift_π _ _ j

/-- 概要：逆比較と元の射影への右随伴の合成は後合成した図式の射影。
方針：随伴の標的自然性と end の持ち上げの式で計算する。
規約：厳密な等式。
使われ方：HA §1.4.2。両比較の逆関係の検査。 -/
@[reassoc (attr := simp)]
theorem fromEnd_π (j : J) : fromEnd adj D ≫ R.map (end_.π D j) =
    end_.π (postDiagram R D) j := by
  rw [fromEnd, ← adj.homEquiv_naturality_right, end_.lift_π, Equiv.apply_symm_apply]

/-- 概要：右随伴と end の交換は通常の圏の同型。
方針：各射影と随伴の Hom 同値の単射性で両合成を検証する。
規約：モデル構造やホモトピー極限の性質を使わない。
使われ方：HA §1.4.2、BF 1978 §2。点つき weighted end の通常の極限との交換。 -/
def iso : R.obj (end_ D) ≅ end_ (postDiagram R D) where
  hom := toEnd D
  inv := fromEnd adj D
  hom_inv_id := by
    apply (adj.homEquiv _ _).symm.injective
    apply end_.hom_ext
    intro j
    rw [adj.homEquiv_naturality_left_symm, Category.assoc,
      ← adj.homEquiv_naturality_right_symm, fromEnd_π,
      ← adj.homEquiv_naturality_left_symm, toEnd_π,
      ← adj.homEquiv_naturality_right_symm, Category.id_comp]
  inv_hom_id := by
    apply end_.hom_ext
    intro j
    rw [Category.assoc, toEnd_π, fromEnd_π, Category.id_comp]

end

end SerrePositivity.KST.Spectra.EndRightAdjoint
