module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PointIdentityConeTransport
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.SliceIdentityTerminal

/-!
概要：元の点 fiber の第二成分の任意の slice 頂点の像は恒等錐、従って終対象。
方針：点射を同じ頂点への定値射とし、元の引き戻しの可換式を使う。
規約：点射に小余極限保存を要求しない。
使われ方：fiber の全小試験図式の両成分余錐の全比較。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：元の任意の点射の恒等錐は同じ点射上の slice の終対象。
方針：Yoneda 表示の恒等錐の終対象性を固定点の厳密同型で移す。
規約：固定点射を変更しない。
使われ方：元の fiber の底の恒等錐の終対象性。 -/
lemma pointIdentityCone_isTerminal {C : SSet.{u}} [Quasicategory C]
    (a : (Δ[0] : SSet.{u}) ⟶ C) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pointIdentityCone a) := by
  have ha : SSet.yonedaEquiv.symm (SSet.yonedaEquiv a) = a := Equiv.symm_apply_apply _ _
  have ht := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceIdentityCone_isTerminalVertex (SSet.yonedaEquiv a)).map_of_isIso
    (eqToHom (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver ha))
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pointIdentityCone_yoneda, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pointIdentityCone_eqToHom ha] at ht
  exact ht

/-- 概要：元の点 fiber の第二成分の全 slice 頂点は元の共通底の恒等錐へ送られる。
方針：点射の定値表示と引き戻しの元の可換式を使う。
規約：実際の slice 頂点の厳密な等式。
使われ方：第二成分の余錐の像の終対象性。 -/
lemma pullbackSliceBaseMap_point_vertex {E B : SSet.{u}}
    (p : E ⟶ B) (q : (Δ[0] : SSet.{u}) ⟶ B)
    (x : (Δ[0] : SSet.{u}) ⟶ pullback p q)
    (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (x ≫ pullback.snd p q)) _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pullbackSliceBaseMap p q x).app (Opposite.op ⦋0⦌) v =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pointIdentityCone ((x ≫ pullback.fst p q) ≫ p) := by
  have hxd : x ≫ pullback.snd p q = 𝟙 (Δ[0] : SSet.{u}) :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  have hbase : (x ≫ pullback.fst p q) ≫ p = q := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hxd, Category.id_comp]
  have hq : q = SSet.const (SSet.yonedaEquiv q) := by
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_const]
  apply Subtype.ext
  change v.val ≫ q = SSet.const (SSet.yonedaEquiv ((x ≫ pullback.fst p q) ≫ p))
  rw [hbase]
  exact (congrArg (fun f : (Δ[0] : SSet.{u}) ⟶ B ↦ v.val ≫ f) hq).trans
    (SSet.comp_const v.val (SSet.yonedaEquiv q))

/-- 概要：元の点 fiber の第二成分の任意の slice 頂点の像は終対象。
方針：元の恒等錐の厳密な回収を使う。
規約：第二脚の保存条件を仮定しない。
使われ方：μ-small 全余錐の像を固定標的の終対象余錐として比較する。 -/
lemma pullbackSliceBaseMap_point_isTerminal {E B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) (q : (Δ[0] : SSet.{u}) ⟶ B)
    (x : (Δ[0] : SSet.{u}) ⟶ pullback p q)
    (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (x ≫ pullback.snd p q)) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pullbackSliceBaseMap p q x).app (Opposite.op ⦋0⦌) v) := by
  rw [pullbackSliceBaseMap_point_vertex]
  exact pointIdentityCone_isTerminal _

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
