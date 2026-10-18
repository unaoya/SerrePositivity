module

public import SerrePositivity.KST.Comparison.ExInfinitySimplicialMonoid
public import SerrePositivity.KST.Comparison.MonoidComponentMaps

/-!
# 群状単体的モノイドの Kan 置換

概要：単体的モノイドの Ex∞ 置換は実際の π₀ モノイドを保ち、群状性を保つ。
方針：基礎射の局所化での可逆性と連結成分のモノイド同型を使う。
規約：KST Lemma 2.13、Segal 1974 Proposition 1.5 の入力の Kan な模型。
使われ方：群状モノイドの bar を Kan な積座標で扱う。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory SSet

/--
概要：群状性を判定する π₀ のモノイドは Ex∞ の置換で同型となる。
方針：単位の基礎射の局所化での可逆性を連結成分のモノイド射に適用する。
規約：乗法は実際の零次単体から誘導したものを使う。
使われ方：元と Kan なモノイドの成分の比較。
-/
def exInfinitySimplicialMonoid_componentsMulEquiv (M : SimplicialObject MonCat.{u}) :
    letI := SimplicialMonoid.componentsMonoid M
    letI := SimplicialMonoid.componentsMonoid (exInfinitySimplicialMonoidFunctor.obj M)
    π₀ (monoidSpace M) ≃* π₀ (monoidSpace (exInfinitySimplicialMonoidFunctor.obj M)) :=
  SimplicialMonoid.componentsMulEquiv (exInfinitySimplicialMonoidUnit.app M) inferInstance

/--
概要：群状単体的モノイドの Ex∞ 置換も群状である。
方針：連結成分の全単射と元の各成分の単元性を使う。
規約：各次数の群構造は要求しない。
使われ方：Segal の比較の Kan なモノイドの入力。
-/
theorem exInfinitySimplicialMonoid_isGrouplike (M : SimplicialObject MonCat.{u})
    (hM : SimplicialMonoid.IsGrouplike M) :
    SimplicialMonoid.IsGrouplike (exInfinitySimplicialMonoidFunctor.obj M) := by
  let := SimplicialMonoid.componentsMonoid M
  let := SimplicialMonoid.componentsMonoid (exInfinitySimplicialMonoidFunctor.obj M)
  exact SimplicialMonoid.isGrouplike_of_components_surjective
    (exInfinitySimplicialMonoidUnit.app M) hM (exInfinitySimplicialMonoid_componentsMulEquiv M).surjective

end SerrePositivity.KST.Comparison
