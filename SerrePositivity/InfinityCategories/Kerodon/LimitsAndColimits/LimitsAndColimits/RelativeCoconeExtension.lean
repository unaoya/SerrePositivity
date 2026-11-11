module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeCoconeRestriction
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeConeFamilies

/-!
概要：相対余錐の局所充填から、指定部分と底を保つ余錐の族を延長する。
方針：相対余錐制限への持ち上げ問題を相対骨格で解き、uncurry で実際の図式へ戻す。
規約：指定部分は全頂点を含み、新しい単体の始点でのみ普遍性を要求する。
使われ方：Kerodon Proposition 7.1.8.7（Tag 06A5） の局所充填を相対 Kan の存在へ渡す。

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

/-- 概要：図式と底の余錐を固定し、新しい単体の始点の相対充填性から余錐の族を延長する。
方針：二つの指定を引き戻しへ合わせ、相対骨格の持ち上げを具体的な図式へ戻す。
規約：元の射 U の fibration 性は不要。
使われ方：境界を固定する相対余錐の局所存在。 -/
lemma exists_kanRelativeCocone_extension_of_first_vertices {K D E B : SSet.{u}}
    (U : D ⟶ E) (A : B.Subcomplex)
    (hA : ∀ v : B _⦋0⦌, v ∈ A.obj (Opposite.op ⦋0⦌))
    (a : (A : SSet.{u}) ⟶ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K (Δ[0] : SSet.{u}))).obj D)
    (d : B ⟶ (ihom K).obj D)
    (g : B ⟶ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K (Δ[0] : SSet.{u}))).obj E)
    (h : d ≫ (ihom K).map U = g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction K E)
    (ha : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction K D = A.ι ≫ d)
    (hg : a ≫ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K (Δ[0] : SSet.{u}))).map U = A.ι ≫ g)
    (ht : ∀ (n : ℕ) (s : B _⦋n + 1⦌), s ∉ A.obj (Opposite.op ⦋n + 1⦌) →
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.KanRelativeCoconeLifting U (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanCoconeFamilyAt a ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexFirstVertex s, hA _⟩)) :
    ∃ H : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K (Δ[0] : SSet.{u}) ⊗ B ⟶ D,
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K (Δ[0] : SSet.{u}) ◁ A.ι) ≫ H = uncurry a ∧
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K (Δ[0] : SSet.{u}) ▷ B) ≫ H = uncurry d ∧ H ≫ U = uncurry g := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanRelativeCocone_lift_iff U A.ι a d g h).1
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.F1BFunctorCategoriesRelativeInitialExtension.exists_lift_of_initial_first_vertices A hA (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanRelativeCoconeRestriction K U) a
    (pullback.lift d g h)
  · apply pullback.hom_ext
    · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanRelativeCoconeRestriction_fst, Category.assoc, pullback.lift_fst]
      exact ha
    · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanRelativeCoconeRestriction_snd, Category.assoc, pullback.lift_snd]
      exact hg
  · intro n s hs
    have hx := ht n s hs
    dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.KanRelativeCoconeLifting] at hx
    rwa [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanCoconeFamilyAt_vertex] at hx

/-- 概要：各点が相対余錐の充填条件を満たす族は、部分パラメータを固定しても相対始対象。
方針：各点の余錐と元の族の頂点の同定を相対内部 Hom の判定へ渡す。
規約：U とパラメータに fibration 性や quasicategory 性は要求しない。
使われ方：相対 Kan の局所普遍余錐の族の相対境界充填。 -/
lemma kanInitialBoundaryLifting_relativeCoconeFamily {J K D E : SSet.{u}}
    (U : D ⟶ E) (A : K.Subcomplex)
    (sq : internalHom.PullbackObjObj A.ι (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanRelativeCoconeRestriction J U))
    (f : K ⟶ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join J (Δ[0] : SSet.{u}))).obj D)
    (hf : ∀ k : K _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.KanRelativeCoconeLifting U (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanCoconeFamilyAt f k)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting sq.π (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialBoundaryLifting_relativeFunctor_of_pointwise A
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanRelativeCoconeRestriction J U) sq f
  intro k
  have h := hf k
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.KanRelativeCoconeLifting] at h
  rwa [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanCoconeFamilyAt_vertex] at h

/-- 概要：自明 Kan fibration 上では全ての余錐が相対余錐の充填条件を満たす。
方針：相対余錐制限の全境界持ち上げを使う。
規約：余錐自体が絶対的な余極限であることは要求しない。
使われ方：相対条件と絶対条件の区別、および標的の同型の場合。 -/
lemma kanRelativeCoconeLifting_of_trivialKanFibration {K D E : SSet.{u}}
    (U : D ⟶ E) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration U] {p : K ⟶ D} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.KanRelativeCoconeLifting U c := by
  intro n a b _ sq
  have : HasLiftingProperty (boundary (n + 1)).ι (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanRelativeCoconeRestriction K U) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanRelativeCoconeRestriction K U) _ inferInstance
  exact ⟨sq.lift, sq.fac_left, sq.fac_right⟩

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
