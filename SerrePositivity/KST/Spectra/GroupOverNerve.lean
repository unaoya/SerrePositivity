module

public import SerrePositivity.KST.Spectra.GroupOverCodiscrete
public import Mathlib.AlgebraicTopology.SimplicialSet.NerveCodiscrete

/-!
概要：一対象群圏の over 圏の nerve と群の元の codiscrete nerve の実際の同型。
方針：射の宇宙が異なる二圏の比較を各次数の composable arrows に直接適用する。
規約：両 nerve の単体の宇宙は u。圏の同値だけでなく単体集合の同型を構成する。
使われ方：Goerss–Jardine VIII §2。Bousfield–Kan の重みを EG の座標へ移す比較。
-/

@[expose] public section

universe u

open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra.GroupOverCodiscrete

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (G : Type u) [Group G]

/-- 概要：over 圏の nerve の各頂点の終点への射を群の元として読む。
方針：over 圏から codiscrete 圏への関手を composable arrows へ送る。
規約：Hom の宇宙の相違を各次数の具体的な射で扱う。
使われ方：Goerss–Jardine VIII §2。重みの頂点座標への順射。 -/
def toNerve (i : AsSmall.{u} (SingleObj G)) : nerve (Over i) ⟶ nerve (Codiscrete G) where
  app n := ↾fun σ ↦ ((toCodiscrete G i).mapComposableArrows n.unop.len).obj σ

/-- 概要：群の元を持つ頂点列から over 圏の nerve の単体を復元する。
方針：群の除法で三角形の射を復元する関手を適用する。
規約：顔・退化との可換性は関手の合成から従う。
使われ方：Goerss–Jardine VIII §2。重みの比較の逆射。 -/
def fromNerve (i : AsSmall.{u} (SingleObj G)) : nerve (Codiscrete G) ⟶ nerve (Over i) where
  app n := ↾fun σ ↦ ((fromCodiscrete G i).mapComposableArrows n.unop.len).obj σ

/-- 概要：群圏の over nerve は codiscrete nerve と実際に同型。
方針：対象の復元と平行射の一意性を nerve の単体の外延性で使う。
規約：有限性・Kan 性はこの同型には不要。
使われ方：Goerss–Jardine VIII §2。hG の重みの同型の各成分。 -/
def nerveIso (i : AsSmall.{u} (SingleObj G)) : nerve (Over i) ≅ nerve (Codiscrete G) where
  hom := toNerve G i
  inv := fromNerve G i
  hom_inv_id := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro σ
    apply nerve.ext_of_isThin
    funext j
    exact from_to_obj G i (σ.obj j)
  inv_hom_id := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro σ
    apply nerve.ext_of_isThin
    rfl

end

end SerrePositivity.KST.Spectra.GroupOverCodiscrete
