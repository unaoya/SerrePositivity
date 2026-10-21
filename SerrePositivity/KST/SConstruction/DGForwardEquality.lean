module
public import SerrePositivity.KST.SConstruction.SimplexHARawWordComposition

/-! # 元の豊穣順斉次合成の添字・結合比較
概要：元の対象・次数・斉次元の一致と結合則を、同じ豊穣順合成へ移す。
方針：対象と次数の等号を消去し、元の forward の結合則を指定出力次数で使う。
規約：元の因子順を保持。使われ方：内部一端点の HA 値の左右分解。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 元の対象・次数・斉次元が一致すれば、同じ豊穣順合成も異種等号で一致する。 -/
lemma dgForward_heq {x y z x' y' z' : D} {p q k p' q' k' : ℤ}
    (hx : x = x') (hy : y = y') (hz : z = z')
    (hp : p = p') (hq : q = q') (hk : k = k')
    (f : GradedHom A x y p) (f' : GradedHom A x' y' p')
    (g : GradedHom A y z q) (g' : GradedHom A y' z' q')
    (hs : p + q = k) (hs' : p' + q' = k') (hf : HEq f f') (hg : HEq g g') :
    HEq (forward A f g hs) (forward A f' g' hs') := by
  cases hx
  cases hy
  cases hz
  cases hp
  cases hq
  cases hk
  cases hf
  cases hg
  rfl

/-- 元の豊穣順合成の結合則は、元の両出力次数を別名にしても一致する。 -/
lemma dgForward_assoc_heq {w x y z : D} {p q r a b k l : ℤ}
    (f : GradedHom A w x p) (g : GradedHom A x y q) (h : GradedHom A y z r)
    (ha : p + q = a) (hb : q + r = b) (hk : a + r = k) (hl : p + b = l) :
    HEq (forward A (forward A f g ha) h hk) (forward A f (forward A g h hb) hl) := by
  have he : k = l := by omega
  cases he
  exact heq_of_eq (forward_assoc_of_sum A f g h ha hb hk)

end SerrePositivity.KST.SConstruction
