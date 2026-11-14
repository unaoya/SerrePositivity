module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.Cocone

/-! # 等しい図式の上での余錐の読み替え

概要：等しい二つの図式の余錐を、写像と頂点を変えずに読み替え、余極限性を保存する。
方針：左因子上の固定条件だけを等式で合成し、余極限性は図式の等式の消去で移す。
規約：HTT §1.2.13。使われ方：任意の四角形の span を chain map の標準表示へ合わせる。
-/

@[expose] public section

universe u

namespace SerrePositivity.InfinityCategories.Project.DerivedCategories

open CategoryTheory

/-- 概要：q 上の余錐を p=q という等式に沿って p 上の余錐に読み替える。
方針：余錐の写像は固定し、固定条件の等式だけを合成する。
規約：HTT §1.2.13。使われ方：span の標準表示への余錐の移送。 -/
def rebaseCocone {K X : SSet.{u}} {p q : K ⟶ X} (h : p = q) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone q) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p :=
  ⟨c.val, c.property.trans h.symm⟩

/-- 概要：図式を等式で読み替えても余錐の頂点は変わらない。
方針：頂点の定義は余錐の写像だけに依存する。
規約：HTT §1.2.13。使われ方：比較射の始域を元の四角形の頂点と同じに保つ。 -/
lemma rebaseCocone_vertex {K X : SSet.{u}} {p q : K ⟶ X} (h : p = q) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone q) :
    (rebaseCocone h c).vertex = c.vertex := rfl

/-- 概要：等しい図式への読み替えは余錐の余極限性を保つ。
方針：図式の等式を消去し、固定条件の証明の一意性を使う。
規約：HTT §1.2.13。使われ方：任意の押し出し四角形を標準 span 上の余極限余錐として読む。 -/
lemma rebaseCocone_isColimit {K X : SSet.{u}} {p q : K ⟶ X} (h : p = q) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone q)
    (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (rebaseCocone h c) := by
  cases h
  exact hc

/-- 図式の読み替えは余極限性を両方向に保存する。 -/
lemma rebaseCocone_isColimit_iff {K X : SSet.{u}} {p q : K ⟶ X} (h : p = q)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone q) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (rebaseCocone h c) ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c := by
  cases h
  rfl
end SerrePositivity.InfinityCategories.Project.DerivedCategories
