module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoreLimit

/-! # 等しい図式の上での錐の読み替え

概要：等しい二つの図式の錐を、写像と頂点を変えずに読み替え、極限性を保存する。
方針：右因子上の固定条件だけを等式で合成し、極限性は図式の等式の消去で移す。
規約：HTT §1.2.13。使われ方：任意の四角形の cospan を chain map の標準表示へ合わせる。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section

universe u

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open CategoryTheory

/-- 概要：q 上の錐を p=q という等式に沿って p 上の錐に読み替える。
方針：錐の写像は固定し、固定条件の等式だけを合成する。
規約：HTT §1.2.13。使われ方：cospan の標準表示への錐の移送。 -/
def rebaseCone {K X : SSet.{u}} {p q : K ⟶ X} (h : p = q) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone q) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p :=
  ⟨c.val, c.property.trans h.symm⟩

/-- 概要：図式を等式で読み替えても錐の頂点は変わらない。
方針：頂点の定義は錐の写像だけに依存する。
規約：HTT §1.2.13。使われ方：比較射の始域を元の四角形の頂点と同じに保つ。 -/
lemma rebaseCone_vertex {K X : SSet.{u}} {p q : K ⟶ X} (h : p = q) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone q) :
    (rebaseCone h c).vertex = c.vertex := rfl

/-- 概要：等しい図式への読み替えは錐の極限性を保つ。
方針：図式の等式を消去し、固定条件の証明の一意性を使う。
規約：HTT §1.2.13。使われ方：任意の引き戻し四角形を標準 cospan 上の極限錐として読む。 -/
lemma rebaseCone_isLimit {K X : SSet.{u}} {p q : K ⟶ X} (h : p = q) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone q)
    (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (rebaseCone h c) := by
  cases h
  exact hc

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
