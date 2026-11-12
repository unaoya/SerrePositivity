module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeFunctorBoundary
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeFamily
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：図式と標的での余錐を同時に固定する相対余錐制限。
方針：内部 Hom の前合成と後合成の可換四角形の引き戻しへの比較を取る。
規約：U に fibration 性を仮定せず、厳密な持ち上げ条件を定式化する。
使われ方：相対 Kan 拡張の局所余錐の存在と境界充填。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 概要：部分図式と標的での全余錐を合わせる引き戻し。
方針：二つの指定の K 上での像が一致する条件を引き戻しで表す。
規約：第一成分が D の図式、第二成分が E の余錐。
使われ方：相対余錐制限の標的。 -/
abbrev KanRelativeCoconeTarget (K : SSet.{u}) {D E : SSet.{u}} (U : D ⟶ E) : SSet.{u} :=
  pullback ((ihom K).map U) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction K E)

/-- 概要：余錐から、その図式と標的での全余錐への相対制限。
方針：前合成の自然性で二成分を引き戻しへ合わせる。
規約：定義に普遍性は含めない。
使われ方：Kerodon Proposition 7.1.6.13（Tag 02XB） の余錐側の比較射。 -/
def kanRelativeCoconeRestriction (K : SSet.{u}) {D E : SSet.{u}} (U : D ⟶ E) :
    (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K (Δ[0] : SSet.{u}))).obj D ⟶ KanRelativeCoconeTarget K U :=
  pullback.lift (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction K D) ((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K (Δ[0] : SSet.{u}))).map U)
    ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K (Δ[0] : SSet.{u}))).naturality U).symm

/-- 概要：U が inner fibration なら相対余錐制限も inner fibration。
方針：単射と inner fibration の相対内部 Hom の判定を使う。
規約：K と底 E の quasicategory 性は不要。
使われ方：相対普遍性を写像空間の条件へ接続する際の充填性。 -/
instance kanRelativeCoconeRestriction_innerFibration (K : SSet.{u}) {D E : SSet.{u}}
    (U : D ⟶ E) [InnerFibration U] : InnerFibration (kanRelativeCoconeRestriction K U) := by
  let sq := Functor.PullbackObjObj.ofHasPullback internalHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K (Δ[0] : SSet.{u})) U
  change InnerFibration sq.π
  exact innerFibration_pullbackObjObjπ sq

/-- 概要：U が自明 Kan fibration なら相対余錐制限も自明 Kan fibration。
方針：左包含の単射性と相対内部 Hom の全境界充填を使う。
規約：添字と値域に充填性を要求しない。
使われ方：相対余錐の条件が標的の指定を保つことの基本例。 -/
instance kanRelativeCoconeRestriction_trivialKanFibration (K : SSet.{u}) {D E : SSet.{u}}
    (U : D ⟶ E) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration U] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (kanRelativeCoconeRestriction K U) := by
  let sq := Functor.PullbackObjObj.ofHasPullback internalHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K (Δ[0] : SSet.{u})) U
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration sq.π
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.trivialKanFibration_pullbackObjObjπ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K (Δ[0] : SSet.{u})) U sq

/-- 概要：相対余錐制限の第一成分は元の図式への制限。
方針：引き戻しの第一射影の式。
規約：厳密な射の等式。
使われ方：部分図式を固定する持ち上げ条件。 -/
lemma kanRelativeCoconeRestriction_fst (K : SSet.{u}) {D E : SSet.{u}} (U : D ⟶ E) :
    kanRelativeCoconeRestriction K U ≫
      pullback.fst ((ihom K).map U) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction K E) = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction K D :=
  pullback.lift_fst _ _ _

/-- 概要：相対余錐制限の第二成分は U による全余錐の像。
方針：引き戻しの第二射影の式。
規約：頂点の像だけでなく全余錐を保持する。
使われ方：底 E の上の指定された図式を固定する。 -/
lemma kanRelativeCoconeRestriction_snd (K : SSet.{u}) {D E : SSet.{u}} (U : D ⟶ E) :
    kanRelativeCoconeRestriction K U ≫
      pullback.snd ((ihom K).map U) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction K E) =
        (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K (Δ[0] : SSet.{u}))).map U :=
  pullback.lift_snd _ _ _

/-- 概要：余錐が相対余錐制限に対して始点境界を充填する条件。
方針：関手単体集合の頂点として余錐全体を指定する。
規約：標準の U-colimit との比較は別定理であり、定義から仮定しない。
使われ方：局所存在の組み立てに必要な操作的な相対普遍性。 -/
def KanRelativeCoconeLifting {K D E : SSet.{u}} (U : D ⟶ E) {p : K ⟶ D}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) : Prop :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting (kanRelativeCoconeRestriction K U) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex c.val)

/-- 概要：相対余錐制限の持ち上げは三つの指定を保つ実際の図式の延長と同値。
方針：二つの射影へ合成し、curry と uncurry の自然性を使う。
規約：部分パラメータ上の全余錐、K 上の図式、E 上の全余錐を厳密に固定する。
使われ方：相対 Kan の局所持ち上げを具体的な余錐の族へ戻す。 -/
@[kerodon 069Q]
lemma kanRelativeCocone_lift_iff {K D E A B : SSet.{u}} (U : D ⟶ E) (i : A ⟶ B)
    (a : A ⟶ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K (Δ[0] : SSet.{u}))).obj D)
    (d : B ⟶ (ihom K).obj D)
    (g : B ⟶ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K (Δ[0] : SSet.{u}))).obj E)
    (h : d ≫ (ihom K).map U = g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction K E) :
    (∃ l : B ⟶ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K (Δ[0] : SSet.{u}))).obj D,
      i ≫ l = a ∧ l ≫ kanRelativeCoconeRestriction K U = pullback.lift d g h) ↔
    ∃ H : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K (Δ[0] : SSet.{u}) ⊗ B ⟶ D,
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K (Δ[0] : SSet.{u}) ◁ i) ≫ H = uncurry a ∧
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K (Δ[0] : SSet.{u}) ▷ B) ≫ H = uncurry d ∧ H ≫ U = uncurry g := by
  constructor
  · rintro ⟨l, hla, hl⟩
    refine ⟨uncurry l, ?_, ?_, ?_⟩
    · rw [← uncurry_natural_left, hla]
    · have hf := congrArg (fun z ↦ z ≫
        pullback.fst ((ihom K).map U) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction K E)) hl
      rw [Category.assoc, kanRelativeCoconeRestriction_fst, pullback.lift_fst] at hf
      have hh := congrArg uncurry hf
      change uncurry (l ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K (Δ[0] : SSet.{u}))).app D) = uncurry d at hh
      rw [uncurry_pre_app] at hh
      exact hh
    · have hs := congrArg (fun z ↦ z ≫
        pullback.snd ((ihom K).map U) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction K E)) hl
      rw [Category.assoc, kanRelativeCoconeRestriction_snd, pullback.lift_snd] at hs
      have hh := congrArg uncurry hs
      rw [uncurry_natural_right] at hh
      exact hh
  · rintro ⟨H, ha, hd, hg⟩
    refine ⟨curry H, ?_, ?_⟩
    · apply uncurry_injective
      rw [uncurry_natural_left, uncurry_curry]
      exact ha
    · apply pullback.hom_ext
      · rw [Category.assoc, kanRelativeCoconeRestriction_fst, pullback.lift_fst]
        apply uncurry_injective
        change uncurry (curry H ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K (Δ[0] : SSet.{u}))).app D) = _
        rw [uncurry_pre_app, uncurry_curry]
        exact hd
      · rw [Category.assoc, kanRelativeCoconeRestriction_snd, pullback.lift_snd]
        apply uncurry_injective
        rw [uncurry_natural_right, uncurry_curry]
        exact hg

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
