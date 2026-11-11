module
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.SquareTranspose
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionComparisonIso

/-! # Suspension 四角形の二枝の交換

概要：suspension 四角形を転置し、元と同じ始点・終点を持つ suspension とする。
方針：二つの零角を交換し、押し出しの転置不変性を使う。
規約：交換の負号との関係は別途証明する。使われ方：三角形の回転の符号。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：同じ始点の suspension 四角形は、四角形そのものが等しければ等しい。
方針：残りの構造は全て命題の証明である。
規約：始点は固定。使われ方：二回の転置の等号。 -/
lemma suspensionSquare_eq_of_square_eq {X : SSet.{u}} {x : X _⦋0⦌}
    (s r : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare x) (h : s.square = r.square) : s = r := by
  rcases s with ⟨⟨S, hzS⟩, hs, hoS, hpS⟩
  rcases r with ⟨⟨R, hzR⟩, hr, hoR, hpR⟩
  change S = R at h
  subst R
  rfl

/-- 概要：二つの零枝を交換した suspension 四角形。
方針：四角形の二座標を転置する。
規約：始点と suspension 頂点は同じ。使われ方：交換作用の定義。 -/
def SuspensionSquare.transpose {X : SSet.{u}} {x : X _⦋0⦌}
    (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare x) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare x where
  square := (β_ (Δ[1] : SSet.{u}) Δ[1]).hom ≫ s.square
  zero_corner := by
    change _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex s.square 1 0)
    exact s.other_zero
  source_eq := s.source_eq
  other_zero := by
    change _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex s.square 0 1)
    exact s.zero_corner
  isPushout := (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.isPushoutSquare_iff_transpose s.square).1 s.isPushout

/-- 概要：suspension 四角形の二回の転置は元に戻る。
方針：二度の座標交換を各単体で計算する。
規約：構造体の等号。使われ方：交換作用の二乗。 -/
lemma SuspensionSquare.transpose_transpose {X : SSet.{u}} {x : X _⦋0⦌}
    (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare x) : s.transpose.transpose = s := by
  apply suspensionSquare_eq_of_square_eq
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro p
  rfl

/-- 概要：転置しても suspension 頂点は同じである。
方針：右上の二座標はどちらも一。
規約：定義からの等号。使われ方：同じ対象上の交換作用。 -/
lemma SuspensionSquare.transpose_vertex {X : SSet.{u}} {x : X _⦋0⦌}
    (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare x) : s.transpose.vertex = s.vertex := rfl

/-- 概要：二つの零枝の交換が suspension 頂点に誘導する標準自己同型。
方針：元の四角形から転置した四角形への標準比較を使う。
規約：負の恒等射との一致はまだ主張しない。使われ方：回転三角形の負号の同定。 -/
def SuspensionSquare.swapIso {X : SSet.{u}} [Quasicategory X]
    {x : X _⦋0⦌} (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare x) :
    (SSet.HomotopyCategory.mk s.vertex : hoFunctor.obj X) ≅ SSet.HomotopyCategory.mk s.vertex :=
  s.comparisonIso s.transpose

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
