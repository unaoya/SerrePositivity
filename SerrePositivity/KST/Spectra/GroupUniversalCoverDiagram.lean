module

public import SerrePositivity.KST.Spectra.GroupActionCochains
public import SerrePositivity.KST.Spectra.GroupOverNerve

/-!
概要：EG の完全な単体集合の作用図式と各次数の離散重みの比較。
方針：単体的 G 集合の二つの添字を交換し、codiscrete nerve の頂点列の表示を使う。
規約：宇宙を揃えた一対象群圏を添字にする。
使われ方：Goerss–Jardine VIII §2。hG の重みと cochain の重みの橋渡し。
-/

@[expose] public section

universe u

open CategoryTheory SSet Opposite

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：単体集合の図式の各次数を離散単体集合にした単体的な重み。
方針：図式の添字と単体次数を交換してから離散単体集合の関手を後合成する。
規約：元の各単体集合の顔・退化を保持する。
使われ方：Goerss–Jardine VIII §§1–2。通常の Tot と単体集合の重みの比較。 -/
def discreteLevels {I : Type u} [SmallCategory I] (W : I ⥤ SSet.{u}) :
    SimplicialObject (I ⥤ SSet.{u}) :=
  Functor.flip W ⋙ (Functor.whiskeringRight I (Type u) SSet.{u}).obj
    (Functor.const (SimplexCategoryᵒᵖ))

namespace GroupActionCochains

/-- 概要：普遍被覆 EG 全体を一対象群圏上の単体集合の作用図式とする。
方針：単体的 G 集合の図式の二つの添字を交換する。
規約：各次数は G^(n+1)、作用は全ての座標への左乗法。
使われ方：Goerss–Jardine VIII §2。equivariant Map(EG,M) の重み。 -/
def universalCoverDiagram (G : Type u) [Group G] : AsSmall.{u} (SingleObj G) ⥤ SSet.{u} :=
  AsSmall.down ⋙ Functor.flip
    (classifyingSpaceUniversalCover G ⋙ Action.FunctorCategoryEquivalence.functor)

/-- 概要：cochain の離散的な EG の重みは EG 全体の各次数の離散化。
方針：二つの構成の対象と射の定義を照合する。
規約：単体的な重みの厳密な等式。
使われ方：Goerss–Jardine VIII §2。Tot と EG の end の比較の係数の同定。 -/
lemma universalCoverWeight_eq_discreteLevels (G : Type u) [Group G] :
    universalCoverWeight G = discreteLevels (universalCoverDiagram G) := rfl

/-- 概要：群の元の codiscrete nerve は EG の完全な単体集合と同型。
方針：codiscrete nerve の各単体を頂点の列と同定する。
規約：添字の対象に依存せず同じ EG を与える。
使われ方：Goerss–Jardine VIII §2。over nerve の頂点座標を EG へ移す。 -/
def codiscreteUniversalCoverIso (G : Type u) [Group G] (i : AsSmall.{u} (SingleObj G)) :
    nerve (Codiscrete G) ≅ (universalCoverDiagram G).obj i :=
  NatIso.ofComponents
    (fun n ↦ (Codiscrete.equivFun (X := G) (n := n.unop.len)).toIso)
    (fun f ↦ by
      ext σ
      rfl)

/-- 概要：群圏上の Bousfield–Kan の重みは EG の作用図式と自然に同型。
方針：over nerve を codiscrete nerve に移し、その頂点列を EG の座標と読む。
規約：群の有限性を仮定しない厳密な図式の同型。
使われ方：Goerss–Jardine VIII §2。hG と群 cochain の Tot の模型比較。 -/
def bousfieldKanUniversalCoverIso (G : Type u) [Group G] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight
      (AsSmall.{u} (SingleObj G)) ≅ universalCoverDiagram G :=
  NatIso.ofComponents
    (fun i ↦ GroupOverCodiscrete.nerveIso G i ≪≫ codiscreteUniversalCoverIso G i)
    (fun f ↦ by
      apply NatTrans.ext
      funext n
      apply ConcreteCategory.hom_ext
      intro σ
      funext k
      rfl)

end GroupActionCochains

end

end SerrePositivity.KST.Spectra
