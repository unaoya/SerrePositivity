module

public import Mathlib.CategoryTheory.SingleObj
public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.CodiscreteCategory

/-!
概要：一対象群圏の over 圏と群の元の codiscrete 圏の具体的な比較。
方針：終点への射を群の元として読み、逆向きの射を群の除法で構成する。
規約：宇宙を揃えた AsSmall の一対象群圏を使う。
使われ方：Goerss–Jardine VIII §2。Bousfield–Kan の重みと EG の重みの同定。
-/

@[expose] public section

universe u

open CategoryTheory

namespace SerrePositivity.KST.Spectra.GroupOverCodiscrete

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (G : Type u) [Group G]

/-- 概要：小さい一対象群圏の標準対象。
方針：元の一対象圏の対象を AsSmall へ持ち上げる。
規約：同圏の対象は全てこの対象に等しい。
使われ方：Goerss–Jardine VIII §2。over 圏の逆向きの構成の始域。 -/
abbrev star : AsSmall.{u} (SingleObj G) := AsSmall.up.obj (SingleObj.star G)

instance index_subsingleton : Subsingleton (AsSmall.{u} (SingleObj G)) := by
  change Subsingleton (ULift.{u} (SingleObj G))
  refine ⟨fun a b ↦ ?_⟩
  apply ULift.ext
  cases a.down
  cases b.down
  rfl

/-- 概要：群圏の over 圏の任意の二つの平行射は等しい。
方針：三角形の可換性を群の左消去で打ち消す。
規約：群の可換性は仮定しない。
使われ方：Goerss–Jardine VIII §2。codiscrete 圏との比較の射の一意性。 -/
instance over_isThin (i : AsSmall.{u} (SingleObj G)) : Quiver.IsThin (Over i) := by
  intro a b
  refine ⟨fun f g ↦ ?_⟩
  apply Over.OverMorphism.ext
  apply ULift.ext
  have h := congrArg (fun t : a.left ⟶ i ↦ (t.down : G)) ((Over.w f).trans (Over.w g).symm)
  let c : G := b.hom.down
  let x : G := f.left.down
  let y : G := g.left.down
  change c * x = c * y at h
  exact mul_left_cancel h

/-- 概要：over 圏の対象を終点への群の元へ送る関手。
方針：codiscrete 圏では全ての対象間の射が一意なので対象の関数だけを与える。
規約：射の群の元は ULift から読み出す。
使われ方：Goerss–Jardine VIII §2。over 圏の nerve の頂点座標。 -/
def toCodiscrete (i : AsSmall.{u} (SingleObj G)) : Over i ⥤ Codiscrete G :=
  Codiscrete.functor (fun a ↦ a.hom.down)

/-- 概要：群の元 g を標準対象から終点への射 g として表す逆向きの関手。
方針：g から h への三角形の射を h⁻¹g で与える。
規約：合成の向きは SingleObj の逆順の乗法の規約に従う。
使われ方：Goerss–Jardine VIII §2。EG の座標から over 圏への復元。 -/
def fromCodiscrete (i : AsSmall.{u} (SingleObj G)) : Codiscrete G ⥤ Over i where
  obj a := Over.mk (show star G ⟶ i from ULift.up a.as)
  map {a b} _ := Over.homMk (ULift.up (b.as⁻¹ * a.as)) (by
    apply ULift.ext
    change b.as * (b.as⁻¹ * a.as) = a.as
    simp only [mul_inv_cancel_left])
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- 概要：群の元から over 圏へ移して戻すと元の codiscrete 図式になる。
方針：対象の復元は定義通り、射は一意性で示す。
規約：自然同型より強い関手の厳密な等式。
使われ方：Goerss–Jardine VIII §2。nerve の実際の同型の一方の逆。 -/
lemma from_to (i : AsSmall.{u} (SingleObj G)) :
    fromCodiscrete G i ⋙ toCodiscrete G i = 𝟭 (Codiscrete G) := by
  exact CategoryTheory.Functor.ext (fun _ ↦ rfl) (fun _ _ _ ↦ Subsingleton.elim _ _)

/-- 概要：over 圏の対象はその群の元から標準始域を用いて復元できる。
方針：一対象圏の対象の一意性で始域を揃えて射を同定する。
規約：終点 i は固定する。
使われ方：Goerss–Jardine VIII §2。over 圏の比較の対象の復元。 -/
lemma from_to_obj (i : AsSmall.{u} (SingleObj G)) (a : Over i) :
    (fromCodiscrete G i).obj ((toCodiscrete G i).obj a) = a := by
  apply CostructuredArrow.obj_ext _ _ (Subsingleton.elim _ _)
  have hl : star G = a.left := Subsingleton.elim _ _
  cases hl
  apply ULift.ext
  change (a.hom.down : G) * 1 = a.hom.down
  exact mul_one _

/-- 概要：over 圏を群の元にして復元すると元の図式になる。
方針：対象の復元と平行射の一意性を関手の外延性へ渡す。
規約：関手の厳密な等式。
使われ方：Goerss–Jardine VIII §2。nerve の実際の同型の他方の逆。 -/
lemma to_from (i : AsSmall.{u} (SingleObj G)) :
    toCodiscrete G i ⋙ fromCodiscrete G i = 𝟭 (Over i) := by
  exact CategoryTheory.Functor.ext (from_to_obj G i) (fun _ _ _ ↦ Subsingleton.elim _ _)

end

end SerrePositivity.KST.Spectra.GroupOverCodiscrete
