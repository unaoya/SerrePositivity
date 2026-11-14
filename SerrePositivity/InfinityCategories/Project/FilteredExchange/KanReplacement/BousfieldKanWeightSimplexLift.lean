module
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.ComposableArrows.Basic


/-!
概要：Bousfield–Kan 重みの単体をその鎖の終点の Over 圏へ持ち上げる。
方針：反対の鎖の最初の対象への射を各頂点の構造射にする。
規約：係数の添字 a を始点として保持する。
使われ方：Over 圏の coend の余極限から元の coend への比較の逆。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange
variable {I : Type u} [SmallCategory I] {a : I} {n : ℕ}

/-- 概要：重みの単体の元の圏での終点。
方針：反対圏の鎖の最初の対象を取る。
規約：零単体にも適用する。使われ方：持ち上げ先の Over 圏。 -/
abbrev bousfieldKanWeightEndpoint (σ : ComposableArrows (Over (Opposite.op a)) n) : I :=
  (σ.obj 0).left.unop

/-- 概要：係数の始点から鎖の終点への射を Over の対象にする。
方針：最初の頂点の構造射を反対にする。
規約：左端は a のまま。使われ方：持ち上げた重みの底。 -/
abbrev bousfieldKanWeightBase (σ : ComposableArrows (Over (Opposite.op a)) n) :
    Over (bousfieldKanWeightEndpoint σ) := Over.mk (σ.obj 0).hom.unop

/-- 概要：鎖の各頂点を終点への射で Over 圏に持ち上げる。
方針：反対の鎖の 0 からの射を反対にする。
規約：左端は元の頂点。使われ方：持ち上げた重みの対象。 -/
abbrev bousfieldKanWeightLiftVertex (σ : ComposableArrows (Over (Opposite.op a)) n)
    (k : Fin (n + 1)) : Over (bousfieldKanWeightEndpoint σ) :=
  Over.mk (σ.map (homOfLE (Fin.zero_le k))).left.unop

/-- 概要：係数の始点から各頂点への射は終点への構造射を保つ。
方針：元の Over の射の可換条件を反対にする。
規約：実際の Over の射を構成する。使われ方：持ち上げた重みの各対象。 -/
def bousfieldKanWeightLiftBaseMap (σ : ComposableArrows (Over (Opposite.op a)) n)
    (k : Fin (n + 1)) : bousfieldKanWeightBase σ ⟶ bousfieldKanWeightLiftVertex σ k :=
  Over.homMk (σ.obj k).hom.unop (by
    exact congrArg Quiver.Hom.unop (Over.w (σ.map (homOfLE (Fin.zero_le k)))))

/-- 概要：鎖の辺を終点への Over 圏の辺に持ち上げる。
方針：関手の合成保存を反対にして構造射との可換性を示す。
規約：反対を戻すので辺の向きが逆になる。使われ方：持ち上げの関手性。 -/
def bousfieldKanWeightLiftArrow (σ : ComposableArrows (Over (Opposite.op a)) n)
    {k l : Fin (n + 1)} (f : k ⟶ l) :
    bousfieldKanWeightLiftVertex σ l ⟶ bousfieldKanWeightLiftVertex σ k :=
  Over.homMk (σ.map f).left.unop (by
    change ((σ.map (homOfLE (Fin.zero_le k))).left ≫ (σ.map f).left).unop = _
    rw [← Over.comp_left, ← σ.map_comp]
    rfl)

/-- 概要：重みの単体を終点の Over 圏上の重みの単体へ持ち上げる。
方針：二段の Over の射を作り、元の鎖の恒等・合成保存を使う。
規約：元の係数 a は持ち上げた底の左端に残る。使われ方：比較の逆の各生成元。 -/
def bousfieldKanWeightSimplexLift (σ : ComposableArrows (Over (Opposite.op a)) n) :
    ComposableArrows (Over (Opposite.op (bousfieldKanWeightBase σ))) n where
  obj k := Over.mk (bousfieldKanWeightLiftBaseMap σ k).op
  map f := Over.homMk (bousfieldKanWeightLiftArrow σ f).op (by
    apply Quiver.Hom.unop_inj
    apply Over.OverMorphism.ext
    exact congrArg Quiver.Hom.unop (Over.w (σ.map f)))
  map_id k := by
    apply Over.OverMorphism.ext
    apply Quiver.Hom.unop_inj
    apply Over.OverMorphism.ext
    simp [bousfieldKanWeightLiftArrow]
  map_comp f g := by
    apply Over.OverMorphism.ext
    apply Quiver.Hom.unop_inj
    apply Over.OverMorphism.ext
    simp [bousfieldKanWeightLiftArrow]

end SerrePositivity.InfinityCategories.Project.FilteredExchange
