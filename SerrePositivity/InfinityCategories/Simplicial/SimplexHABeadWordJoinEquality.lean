module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Simplicial.SimplexHABeadWord

/-! # 元の連結語の両因子の一致の移送
概要：元の端点・自由次元と両因子の一致を、同じ連結語の一致へ移す。
方針：全添字の等号を消去してから元の両因子の異種等号を消去する。
規約：元の因子順を保持。使われ方：任意位置の端点挿入の読み替えの帰納。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Simplicial
open SerrePositivity.KST.SConstruction

/-- 元の端点・自由次元と両因子が一致すれば、同じ順序の連結語も一致する。 -/
lemma simplexHABeadWordJoin_heq {n : ℕ} {a b c a' b' c' : Fin (n + 1)}
    {p q p' q' : ℕ} (ha : a = a') (hb : b = b') (hc : c = c') (hp : p = p') (hq : q = q')
    (l : _root_.SerrePositivity.InfinityCategories.Simplicial.SimplexHABeadWord n a b p) (l' : _root_.SerrePositivity.InfinityCategories.Simplicial.SimplexHABeadWord n a' b' p')
    (r : _root_.SerrePositivity.InfinityCategories.Simplicial.SimplexHABeadWord n b c q) (r' : _root_.SerrePositivity.InfinityCategories.Simplicial.SimplexHABeadWord n b' c' q')
    (hl : HEq l l') (hr : HEq r r') : HEq (l.join r) (l'.join r') := by
  cases ha
  cases hb
  cases hc
  cases hp
  cases hq
  cases hl
  cases hr
  rfl

end SerrePositivity.InfinityCategories.Simplicial

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.simplexHABeadWordJoin_heq := _root_.SerrePositivity.InfinityCategories.Simplicial.simplexHABeadWordJoin_heq
