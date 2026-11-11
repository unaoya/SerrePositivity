module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeHomDiagramExtension
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeJoinInvertingRestriction

/-!
概要：cocartesian fibration 間の単射が誘導する相対指数の制限は inner fibration。
方針：底の射を curry の全単射で固定し、内ホーンと部分図式を同時に保つ延長を使う。
規約：共通の底の quasicategory 性は不要。
使われ方：相対 join の制限射自体の充填性。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：底上の単射による図式の族の制限は inner fibration。
方針：可換正方形を実際の逆像上の整合する図式に戻し、両方を固定して延長する。
規約：両側の元の射影は cocartesian fibration、標的だけ quasicategory。
使われ方：fiber の cartesian 性から制限の全空間の cartesian 性へ移す前提。 -/
instance kanFiberwiseHomPre_innerFibration {C D : SSet.{u}} [Quasicategory D]
    {K L : Over C} (i : K ⟶ L) [Mono i.left]
    [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration K.hom] [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration L.hom] :
    InnerFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomPre (D := D) i) where
  mem := by
    intro A B j hj
    constructor
    intro a b sq
    let c := b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomProjection K.hom D
    have ha : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomProjection L.hom D = j ≫ c := by
      rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.fiberwiseHomPre_projection i, ← Category.assoc, sq.w, Category.assoc]
    let F := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomEquiv (D := D) K.hom c).symm ⟨b, rfl⟩
    let G := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomEquiv (D := D) L.hom (j ≫ c)).symm ⟨a, ha⟩
    have hF : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomCurry K.hom c F = b :=
      congrArg Subtype.val ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomEquiv (D := D) K.hom c).apply_symm_apply ⟨b, rfl⟩)
    have hG : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomCurry L.hom (j ≫ c) G = a :=
      congrArg Subtype.val ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomEquiv (D := D) L.hom (j ≫ c)).apply_symm_apply ⟨a, ha⟩)
    let u : Over.mk (j ≫ c) ⟶ Over.mk c := Over.homMk j rfl
    have hFG : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackUnderlying K.hom).map u ≫ F =
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackMap i (Over.mk (j ≫ c)) ≫ G := by
      apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.fiberwiseHomCurry_injective K.hom (j ≫ c)
      erw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.fiberwiseHomCurry_precomp, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanFiberwiseHomCurry_pre i, hF, hG]
      exact sq.w.symm
    obtain ⟨H, hHK, hHL⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.exists_kanRelativeHomDiagram_extension i u hj F G hFG
    refine CommSq.HasLift.mk' {
      l := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomCurry L.hom c H
      fac_left := ?_
      fac_right := ?_ }
    · rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.fiberwiseHomCurry_precomp]
      change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomCurry L.hom (j ≫ c) ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackUnderlying L.hom).map u ≫ H) = _
      rw [hHL, hG]
    · erw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanFiberwiseHomCurry_pre i, hHK]
      exact hF

/-- 概要：相対 join の左包含は単射。
方針：通常の join への射影に合成すると単射な左包含になる。
規約：元の二つの構造射は任意。
使われ方：相対指数の制限の一般の inner fibration 判定への適用。 -/
instance kanRelativeJoinInl_mono {K L C : SSet.{u}} (p : K ⟶ C) (q : L ⟶ C) :
    Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl p q) := mono_of_mono_fac (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl_fst p q)

/-- 概要：相対 join の図式の族を元の図式へ制限する射自体が inner fibration。
方針：左包含の単射性と両側の底への cocartesian fibration 性を一般の判定に渡す。
規約：底の quasicategory 性は要求しない。
使われ方：V の fiber の cartesian 性を全空間へ移すための前提。 -/
lemma kanRelativeJoinRestriction_innerFibration {K C D : SSet.{u}} [Quasicategory D]
    (p : K ⟶ C) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p] :
    InnerFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomPre (D := D) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinInlOver p)) := by
  have : Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinInlOver p).left :=
    inferInstanceAs (Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl p (𝟙 C)))
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration (Over.mk p).hom := inferInstanceAs (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p)
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration (Over.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinBaseProjection p (𝟙 C))).hom :=
    inferInstanceAs (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinBaseProjection p (𝟙 C)))
  exact kanFiberwiseHomPre_innerFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinInlOver p)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
