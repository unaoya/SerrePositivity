module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeCoconeRestriction
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ColimitRelativeBoundary

/-!
概要：終対象への射の相対余錐充填条件から通常の余極限性を回収する。
方針：終対象に値を持つ内部 Hom の射の一意性で第二成分を消去する。
規約：D の quasicategory 性のみを仮定し、添字は任意。
使われ方：相対余錐の操作的な判定が絶対的な余極限 API を含むことの確認。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：終対象に値を取る関手単体集合への射は一意。
方針：uncurry した二つの射を終対象の一意性で比較する。
規約：パラメータと添字に仮定を置かない。
使われ方：終対象上の相対余錐制限の第二成分の消去。 -/
lemma kanIhom_terminal_hom_ext {A J E : SSet.{u}} (hE : IsTerminal E)
    (f g : A ⟶ (ihom J).obj E) : f = g := by
  apply uncurry_injective
  exact hE.hom_ext _ _

/-- 概要：終対象上の相対余錐充填条件は通常の余極限性と同値。
方針：相対比較の第一射影で絶対条件を取り出し、第二射影の条件は終対象の一意性で示す。
規約：U の標的に終対象性を指定する。
使われ方：絶対的な Kan 拡張の存在定理を相対理論の特殊例として接続する。 -/
lemma kanRelativeCoconeLifting_iff_isColimit_of_terminal {K D E : SSet.{u}}
    [Quasicategory D] (U : D ⟶ E) (hE : IsTerminal E) {p : K ⟶ D} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.KanRelativeCoconeLifting U c ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c := by
  constructor
  · intro hc
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isColimitCone_of_initialBoundaryLifting_coconeRestriction c
    intro n a b ha sq
    let g : (Δ[n + 1] : SSet.{u}) ⟶ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K (Δ[0] : SSet.{u}))).obj E :=
      curry (hE.from (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K (Δ[0] : SSet.{u}) ⊗ Δ[n + 1]))
    let y : (Δ[n + 1] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.KanRelativeCoconeTarget K U :=
      pullback.lift b g (kanIhom_terminal_hom_ext hE _ _)
    have sq' : CommSq a (boundary (n + 1)).ι (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanRelativeCoconeRestriction K U) y := by
      constructor
      apply pullback.hom_ext
      · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanRelativeCoconeRestriction_fst, Category.assoc, pullback.lift_fst]
        exact sq.w
      · exact kanIhom_terminal_hom_ext hE _ _
    obtain ⟨F, hF, hFy⟩ := hc n a y ha sq'
    refine ⟨F, hF, ?_⟩
    have h := congrArg (fun z ↦ z ≫
      pullback.fst ((ihom K).map U) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction K E)) hFy
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanRelativeCoconeRestriction_fst] at h
    simpa only [y, pullback.lift_fst] using h
  · intro hc n a b ha sq
    let f := b ≫ pullback.fst ((ihom K).map U) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction K E)
    have sq' : CommSq a (boundary (n + 1)).ι (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction K D) f := by
      have h := congrArg (fun z ↦ z ≫
        pullback.fst ((ihom K).map U) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction K E)) sq.w
      rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanRelativeCoconeRestriction_fst, Category.assoc] at h
      exact ⟨h⟩
    obtain ⟨F, hF, hFp⟩ := hc.initialBoundaryLifting n a f ha sq'
    refine ⟨F, hF, ?_⟩
    apply pullback.hom_ext
    · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanRelativeCoconeRestriction_fst]
      exact hFp
    · exact kanIhom_terminal_hom_ext hE _ _

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
