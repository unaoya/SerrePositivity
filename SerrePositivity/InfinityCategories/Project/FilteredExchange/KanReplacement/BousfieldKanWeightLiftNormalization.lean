module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.BousfieldKanWeightSimplexLift

/-!
概要：既に Over 圏にある重みの単体を忘却して持ち上げ直す操作の比較。
方針：鎖の終点の構造射で後合成し、底の恒等成分の射で元の重みに戻す。
規約：比較は元の Over 圏の coend の関係式で用いる。
使われ方：標準比較と次数ごとの持ち上げの他方の逆則。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange
variable {I : Type u} [SmallCategory I] {i : I} {a : Over i} {n : ℕ}

/-- 概要：Over 圏上の重みの単体を元の圏の重みへ忘却する。
方針：忘却の反対関手で各 Over の構造を送る。
規約：係数の始点は a.left。使われ方：最小の終点への持ち上げ。 -/
abbrev bousfieldKanWeightForgetSimplex
    (σ : ComposableArrows (Over (Opposite.op a)) n) := σ ⋙ Over.post (Over.forget i).op

/-- 概要：持ち上げ直した底と元の底の間には左成分が恒等の射がある。
方針：最初の頂点の構造射の Over の可換条件を使う。
規約：終点への後合成の後で比較する。使われ方：coend の底の変更。 -/
def bousfieldKanWeightNormalizationBaseMap
    (σ : ComposableArrows (Over (Opposite.op a)) n) :
    a ⟶ (Over.map ((σ.obj 0).left.unop.hom)).obj
      (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.bousfieldKanWeightBase (bousfieldKanWeightForgetSimplex σ)) :=
  Over.homMk (𝟙 a.left) (by
    change (𝟙 a.left) ≫ ((σ.obj 0).hom.unop.left ≫ (σ.obj 0).left.unop.hom) = a.hom
    rw [Category.id_comp]
    exact Over.w (σ.obj 0).hom.unop)

/-- 概要：各頂点の持ち上げ直しを後合成すると元の頂点に一致する。
方針：鎖の辺の Over の可換条件を構造射の等式として使う。
規約：左端の対象は厳密に同じ。使われ方：鎖全体の正規化。 -/
lemma bousfieldKanWeightLiftVertex_normalization
    (σ : ComposableArrows (Over (Opposite.op a)) n) (k : Fin (n + 1)) :
    (Over.map ((σ.obj 0).left.unop.hom)).obj
      (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.bousfieldKanWeightLiftVertex (bousfieldKanWeightForgetSimplex σ) k) =
        (σ.obj k).left.unop := by
  change Over.mk ((σ.map (homOfLE (Fin.zero_le k))).left.unop.left ≫
    (σ.obj 0).left.unop.hom) = (σ.obj k).left.unop
  rw [Over.w]
  rfl

/-- 概要：忘却した単体の持ち上げ直しは底の比較を通して元の単体に戻る。
方針：各頂点の構造射と各辺の左成分を比較する。
規約：同じ重み内での関手の等式。使われ方：次数ごとの他方の逆則。 -/
lemma bousfieldKanWeightSimplexLift_normalization
    (σ : ComposableArrows (Over (Opposite.op a)) n) :
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.bousfieldKanWeightSimplexLift (bousfieldKanWeightForgetSimplex σ) ⋙
      Over.post (Over.map ((σ.obj 0).left.unop.hom)).op ⋙
        Over.map (bousfieldKanWeightNormalizationBaseMap σ).op = σ := by
  refine CategoryTheory.Functor.ext (fun k ↦ ?_) ?_
  · apply CostructuredArrow.obj_ext _ _
      (congrArg Opposite.op (bousfieldKanWeightLiftVertex_normalization σ k))
    apply Quiver.Hom.unop_inj
    apply Over.OverMorphism.ext
    simp [Over.eqToHom_left, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.bousfieldKanWeightSimplexLift,
      _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.bousfieldKanWeightLiftBaseMap, bousfieldKanWeightNormalizationBaseMap]
  · intro k l f
    apply Over.OverMorphism.ext
    apply Quiver.Hom.unop_inj
    apply Over.OverMorphism.ext
    simp [Over.eqToHom_left, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.bousfieldKanWeightSimplexLift,
      _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.bousfieldKanWeightLiftArrow, bousfieldKanWeightNormalizationBaseMap]

end SerrePositivity.InfinityCategories.Project.FilteredExchange
