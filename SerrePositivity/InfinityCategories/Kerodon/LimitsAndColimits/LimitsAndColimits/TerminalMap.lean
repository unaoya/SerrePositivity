module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoreLimit

/-!
概要：trivial Kan fibration と同型による終対象・極限錐の移送。
方針：境界の充填を射の上下で移し、同型による slice の作用を用いる。
規約：弱同値やモデル構造の一般論は使わない。
使われ方：HTT §1.2.12–1.2.13、Kerodon §7.1（Tag 02H1） の通常の圏の nerve での検算。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory SSet MorphismProperty
open scoped Simplicial

namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 概要：同型は trivial Kan fibration。
方針：同型の逆射が全ての持ち上げを与える。
規約：任意の単体集合の同型を扱う。
使われ方：Kerodon §1.5.5（Tag 006V）、同型による終対象の移送。 -/
instance isIso_trivialKanFibration {X Y : SSet.{u}} (q : X ⟶ Y) [IsIso q] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration q where
  mem := MorphismProperty.rlp_of_isIso _ _

/-- 概要：trivial Kan fibration は頂点の終対象性を反映する。
方針：標的で境界を充填し、その充填を全境界の持ち上げ性で持ち上げる。
規約：quasicategory 性は不要。
使われ方：HTT §1.2.12、Kerodon §7.1（Tag 02H1） の極限錐の検算。 -/
lemma isTerminalVertex_of_trivialKanFibration {X Y : SSet.{u}} (q : X ⟶ Y)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration q] {x : X _⦋0⦌} (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (q.app (Opposite.op ⦋0⦌) x)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex x := by
  intro n b hb
  have hy : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1)) ≫ (b ≫ q) =
      SSet.yonedaEquiv.symm (q.app (Opposite.op ⦋0⦌) x) := by
    rw [← Category.assoc, hb, SSet.yonedaEquiv_symm_comp]
  obtain ⟨F, hF⟩ := hx n (b ≫ q) hy
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := q) (boundary (n + 1)).ι inferInstance
  have sq : CommSq b (boundary (n + 1)).ι q F := ⟨hF.symm⟩
  exact ⟨sq.lift, sq.fac_left⟩

/-- 概要：同型による頂点の像は終対象性を保つ。
方針：逆同型の trivial Kan fibration による反映を使う。
規約：quasicategory 性は不要。
使われ方：HTT §1.2.12 の標準単体と nerve の比較。 -/
lemma IsTerminalVertex.map_of_isIso {X Y : SSet.{u}} (q : X ⟶ Y) [IsIso q]
    {x : X _⦋0⦌} (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex x) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (q.app (Opposite.op ⦋0⦌) x) := by
  apply isTerminalVertex_of_trivialKanFibration (inv q)
  have he : (inv q).app (Opposite.op ⦋0⦌) (q.app (Opposite.op ⦋0⦌) x) = x := by
    rw [← NatTrans.comp_app_apply, IsIso.hom_inv_id]
    rfl
  rw [he]
  exact hx

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex export _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsTerminalVertex (map_of_isIso)


/-- 概要：標的の同型による slice の作用は同型。
方針：各錐の後合成を逆射で戻す。
規約：図式 p 自体も同じ射で後合成する。
使われ方：HTT §1.2.13 の標準単体と nerve の極限錐の比較。 -/
lemma sliceOverPostcomp_isIso {K X Y : SSet.{u}} (p : K ⟶ X) (q : X ⟶ Y) [IsIso q] :
    IsIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp p q) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro n
  rw [isIso_iff_bijective]
  constructor
  · intro σ τ h
    apply Subtype.ext
    apply (cancel_mono q).1
    exact congrArg Subtype.val h
  · intro σ
    let τ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p).obj n := ⟨σ.val ≫ inv q, by
      rw [← Category.assoc, σ.property, Category.assoc, IsIso.hom_inv_id, Category.comp_id]⟩
    refine ⟨τ, Subtype.ext ?_⟩
    change (σ.val ≫ inv q) ≫ q = σ.val
    rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]

/-- 概要：図式上の錐は標的の射で後合成できる。
方針：錐の射を後合成し、固定条件も後合成する。
規約：新しい図式は p≫q。
使われ方：HTT §1.2.13 の通常の圏の nerve への移送。 -/
def JoinCone.postcomp {K X Y : SSet.{u}} {p : K ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (q : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (p ≫ q) :=
  ⟨c.val ≫ q, by rw [← Category.assoc, c.property]⟩

/-- 概要：標的の同型による後合成は極限錐を保つ。
方針：同型が誘導する slice の同型に沿って終対象を写す。
規約：追加の quasicategory の仮定は不要。
使われ方：HTT §1.2.13、Kerodon §7.1（Tag 02H1） の通常の圏の nerve での極限の検算。 -/
lemma IsLimitCone.postcomp_of_isIso {K X Y : SSet.{u}} {p : K ⟶ X} {c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p}
    (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c) (q : X ⟶ Y) [IsIso q] : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (c.postcomp q) := by
  have := sliceOverPostcomp_isIso p q
  exact IsTerminalVertex.map_of_isIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp p q) hc

/-- 概要：図式の等式で錐の固定条件を移送する。
方針：錐の射を保ち、固定条件の等式だけを合成する。
規約：図式の等式以外の仮定はない。
使われ方：HTT §1.2.13 の通常の圏の図式の nerve との比較。 -/
def JoinCone.cast {K X : SSet.{u}} {p q : K ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (h : p = q) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone q :=
  ⟨c.val, c.property.trans h⟩

/-- 概要：図式の等式で錐を移送しても頂点は変わらない。
方針：固定条件の証明を使わない頂点の定義を計算する。
規約：錐の射そのものは共通。
使われ方：HTT §1.2.13 の通常の錐との頂点の照合。 -/
lemma JoinCone.vertex_cast {K X : SSet.{u}} {p q : K ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (h : p = q) :
    (c.cast h).vertex = c.vertex := rfl

/-- 概要：錐を標的の射で後合成すると、その頂点も同じ射で写る。
方針：Yoneda の後合成への自然性を使う。
規約：q は任意の単体集合の射。
使われ方：HTT §1.2.13 の標準単体と nerve の錐の比較。 -/
lemma JoinCone.vertex_postcomp {K X Y : SSet.{u}} {p : K ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (q : X ⟶ Y) :
    (c.postcomp q).vertex = q.app (Opposite.op ⦋0⦌) c.vertex := by
  change SSet.yonedaEquiv (_ ≫ (c.val ≫ q)) = _
  rw [← Category.assoc, SSet.yonedaEquiv_comp]
  rfl

/-- 概要：図式の等式による移送は極限性を保つ。
方針：等式で置換し、固定条件の証明の無関係性を使う。
規約：錐の射そのものは変えない。
使われ方：HTT §1.2.13 の具体的な nerve の極限の検算。 -/
lemma IsLimitCone.cast {K X : SSet.{u}} {p q : K ⟶ X} {c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p}
    (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c) (h : p = q) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (c.cast h) := by
  subst q
  exact hc

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
