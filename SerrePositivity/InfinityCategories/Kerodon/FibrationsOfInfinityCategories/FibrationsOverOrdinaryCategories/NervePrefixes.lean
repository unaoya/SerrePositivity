module

public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.Order.Fin.Basic

/-!
概要：weighted nerve に用いる標準単体の初区間の重みとその制限。
方針：有限順序集合の最初の i+1 頂点を標準単体にし、単調写像を各初区間へ制限する。
規約：初区間の最後の頂点 i は重みの添字を兼ねる。
使われ方：Kerodon Definition 5.3.3.1（Tag 025X）、weighted nerve の単体作用素。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 概要：小さい標準単体を大きい標準単体の初区間へ含める順序射。
方針：有限順序集合の castLE の順序埋め込みを使う。
規約：頂点の値を変えない。
使われ方：Kerodon Definition 5.3.3.1（Tag 025X）、weighted nerve の重みの構造射。 -/
def simplexPrefixInclusion (m n : ℕ) (h : m ≤ n) : ⦋m⦌ ⟶ ⦋n⦌ :=
  SimplexCategory.Hom.mk (Fin.castLEOrderEmb (Nat.succ_le_succ h)).toOrderHom

/-- 概要：同じ長さの初区間の包含は恒等射。
方針：各頂点の値を比較する。
規約：h の証明の違いには依存しない。
使われ方：Kerodon Definition 5.3.3.1（Tag 025X）、重みの恒等則。 -/
lemma simplexPrefixInclusion_id (n : ℕ) : simplexPrefixInclusion n n le_rfl = 𝟙 ⦋n⦌ := by
  apply SimplexCategory.Hom.ext
  rfl

/-- 概要：初区間の包含の合成は初区間の包含。
方針：有限順序集合の値が合成で変わらないことを確認する。
規約：h と k は長さの大小関係。
使われ方：Kerodon Definition 5.3.3.1（Tag 025X）、重みの合成則。 -/
lemma simplexPrefixInclusion_comp {l m n : ℕ} (h : l ≤ m) (k : m ≤ n) :
    simplexPrefixInclusion l m h ≫ simplexPrefixInclusion m n k =
      simplexPrefixInclusion l n (h.trans k) := by
  apply SimplexCategory.Hom.ext
  rfl

/-- 概要：初区間の頂点を元の有限順序集合へ戻す。
方針：頂点の自然数の値を保ち、添字 i の上界を使う。
規約：i 自身を含む i+1 個の頂点を扱う。
使われ方：Kerodon Definition 5.3.3.1（Tag 025X）、単調写像の初区間への制限。 -/
def simplexPrefixVertex {n : ℕ} (i : Fin (n + 1)) (k : Fin (i.val + 1)) : Fin (n + 1) :=
  ⟨k.val, lt_of_le_of_lt (Nat.le_of_lt_succ k.isLt) i.isLt⟩

/-- 概要：単調写像を、i 以下の初区間からその像の初区間への射に制限する。
方針：初区間の各頂点に元の単調写像を適用し、単調性で像の上界を確認する。
規約：制限の標的の長さは α(i)。
使われ方：Kerodon Definition 5.3.3.1（Tag 025X）、weighted nerve の τ_i の引き戻し。 -/
def simplexPrefixRestriction {m n : SimplexCategory} (α : m ⟶ n) (i : Fin (m.len + 1)) :
    ⦋i.val⦌ ⟶ ⦋(α.toOrderHom i).val⦌ :=
  SimplexCategory.Hom.mk {
    toFun k := ⟨(α.toOrderHom (simplexPrefixVertex i k)).val, Nat.lt_succ_of_le
      (α.toOrderHom.monotone (show simplexPrefixVertex i k ≤ i from Nat.le_of_lt_succ k.isLt))⟩
    monotone' k l h := α.toOrderHom.monotone (show simplexPrefixVertex i k ≤
      simplexPrefixVertex i l from h) }

/-- 概要：恒等単調写像の初区間への制限は恒等射。
方針：各頂点の値を比較する。
規約：i は任意の頂点。
使われ方：Kerodon Definition 5.3.3.1（Tag 025X）、weighted nerve の恒等作用素。 -/
lemma simplexPrefixRestriction_id (m : SimplexCategory) (i : Fin (m.len + 1)) :
    simplexPrefixRestriction (𝟙 m) i = 𝟙 ⦋i.val⦌ := by
  apply SimplexCategory.Hom.ext
  rfl

/-- 概要：合成単調写像の初区間への制限は二つの制限の合成。
方針：各頂点の自然数の値を計算する。
規約：二つ目の制限の添字は α(i)。
使われ方：Kerodon Definition 5.3.3.1（Tag 025X）、weighted nerve の作用素の合成則。 -/
lemma simplexPrefixRestriction_comp {l m n : SimplexCategory}
    (α : l ⟶ m) (β : m ⟶ n) (i : Fin (l.len + 1)) :
    simplexPrefixRestriction (α ≫ β) i =
      simplexPrefixRestriction α i ≫ simplexPrefixRestriction β (α.toOrderHom i) := by
  apply SimplexCategory.Hom.ext
  rfl

/-- 概要：初区間への制限は初区間の包含と可換。
方針：どちらの合成も元の単調写像を頂点に適用する射であることを確認する。
規約：h は i≤j の関係。
使われ方：Kerodon Definition 5.3.3.1（Tag 025X）、weighted nerve の重みの自然性。 -/
lemma simplexPrefixRestriction_naturality {m n : SimplexCategory} (α : m ⟶ n)
    {i j : Fin (m.len + 1)} (h : i ≤ j) :
    simplexPrefixInclusion i.val j.val h ≫ simplexPrefixRestriction α j =
      simplexPrefixRestriction α i ≫ simplexPrefixInclusion
        (α.toOrderHom i).val (α.toOrderHom j).val (α.toOrderHom.monotone h) := by
  apply SimplexCategory.Hom.ext
  rfl

/-- 概要：単調写像の初区間上の作用は、初区間への制限に続く包含に分解する。
方針：各頂点の値を元の単調写像で計算する。
規約：標的は元の全標準単体 n。
使われ方：Kerodon Definition 5.3.3.1（Tag 025X）、一定の底の上の weighted nerve の単体。 -/
lemma simplexPrefixRestriction_factor {m n : SimplexCategory} (α : m ⟶ n)
    (i : Fin (m.len + 1)) :
    simplexPrefixInclusion i.val m.len (Nat.le_of_lt_succ i.isLt) ≫ α =
      simplexPrefixRestriction α i ≫ simplexPrefixInclusion
        (α.toOrderHom i).val n.len (Nat.le_of_lt_succ (α.toOrderHom i).isLt) := by
  apply SimplexCategory.Hom.ext
  rfl

/-- 概要：各頂点 i に標準 i 単体を置く weighted nerve の重み。
方針：有限順序集合上の射を初区間の包含で写す。
規約：単体集合の宇宙は u、添字は有限型。
使われ方：Kerodon Definition 5.3.3.1（Tag 025X）、τ の族を自然変換として表す始域。 -/
def simplexPrefixWeight (n : ℕ) : Fin (n + 1) ⥤ SSet.{u} where
  obj i := Δ[i.val]
  map {i j} f := stdSimplex.map (simplexPrefixInclusion i.val j.val (leOfHom f))
  map_id i := by
    rw [simplexPrefixInclusion_id, CategoryTheory.Functor.map_id]
  map_comp {i j k} f g := by
    rw [← CategoryTheory.Functor.map_comp, simplexPrefixInclusion_comp]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
