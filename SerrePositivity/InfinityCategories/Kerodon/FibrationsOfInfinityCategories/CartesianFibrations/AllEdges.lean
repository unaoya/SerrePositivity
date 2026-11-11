module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianFibration

/-!
概要：全辺が cartesian・cocartesian である fibration の特徴づけ。
方針：一次ホーンは指定端点の lift、内ホーンは rlp、外ホーンは辺の条件を使う。
規約：底の quasicategory 性は不要。
使われ方：Kerodon Proposition 5.1.4.15（Tag 01UM）、A2d の right/left fibration の回収。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：全辺が cartesian なら cartesian fibration は right fibration。
方針：一次・内側・外側のホーンを分けて充填する。
規約：辺に関する仮定は全ての一単体に課す。
使われ方：Kerodon Proposition 5.1.4.15（Tag 01UM）、A2d のホーンによる定義への逆接続。 -/
lemma rightFibration_of_cartesianFibration_of_all_edges {X B : SSet.{u}}
    (p : X ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianFibration p]
    (h : ∀ e : X _⦋1⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge p e) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration p := by
  constructor
  intro A C f hf
  cases hf with
  | @intro n i h0 =>
    cases n with
    | zero =>
      have hi : i = 1 := by fin_cases i <;> simp_all
      subst i
      constructor
      intro a b sq
      let x := SSet.yonedaEquiv (horn.ι (n := 0) 1 0 (by decide) ≫ a)
      have he : stdSimplex.δ 0 ≫ b =
          SSet.yonedaEquiv.symm (p.app (Opposite.op ⦋0⦌) x) := by
        rw [← SSet.yonedaEquiv_symm_comp]
        dsimp only [x]
        rw [Equiv.symm_apply_apply, Category.assoc, sq.w, horn.ι_ι_assoc]
      obtain ⟨g, hg, hgp, _⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianFibration.mem (p := p) |>.2 x b he
      refine CommSq.HasLift.mk' {
        l := g
        fac_left := ?_
        fac_right := hgp }
      apply horn.hom_ext'
      intro j hj
      fin_cases j
      · rw [horn.ι_ι_assoc]
        change stdSimplex.δ 0 ≫ g = _
        exact hg.trans (SSet.yonedaEquiv.symm_apply_apply _)
      · exact (hj rfl).elim
    | succ n =>
      by_cases hi : i = Fin.last (n + 2)
      · subst i
        constructor
        intro a b sq
        exact h _ n a b rfl sq
      · exact InnerFibration.mem (q := p) _
          (innerHornInclusions.intro i h0 (lt_of_le_of_ne (Fin.le_last _) hi))

/-- 概要：right fibration は全辺が cartesian な cartesian fibration と同値。
方針：既存の接続と全辺からのホーン充填を組み合わせる。
規約：選択した lift を追加のデータとして保持しない。
使われ方：Kerodon Proposition 5.1.4.15（Tag 01UM）、A2d と F1a の定義の互換性。 -/
lemma rightFibration_iff_cartesianFibration_all_edges {X B : SSet.{u}} (p : X ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration p ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianFibration p ∧ ∀ e : X _⦋1⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge p e := by
  constructor
  · intro hp
    have := hp
    exact ⟨inferInstance, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCartesianEdge_of_rightFibration p⟩
  · rintro ⟨hp, he⟩
    have := hp
    exact rightFibration_of_cartesianFibration_of_all_edges p he

/-- 概要：全辺が cocartesian なら cocartesian fibration は left fibration。
方針：一次・内側・外側のホーンを分けて充填する。
規約：辺に関する仮定は全ての一単体に課す。
使われ方：Kerodon Proposition 5.1.4.15（Tag 01UM）、A2d のホーンによる定義への逆接続。 -/
lemma leftFibration_of_cocartesianFibration_of_all_edges {X B : SSet.{u}}
    (p : X ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p]
    (h : ∀ e : X _⦋1⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge p e) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p := by
  constructor
  intro A C f hf
  cases hf with
  | @intro n i hn =>
    cases n with
    | zero =>
      have hi : i = 0 := by fin_cases i <;> simp_all
      subst i
      constructor
      intro a b sq
      let x := SSet.yonedaEquiv (horn.ι (n := 0) 0 1 (by decide) ≫ a)
      have he : stdSimplex.δ 1 ≫ b =
          SSet.yonedaEquiv.symm (p.app (Opposite.op ⦋0⦌) x) := by
        rw [← SSet.yonedaEquiv_symm_comp]
        dsimp only [x]
        rw [Equiv.symm_apply_apply, Category.assoc, sq.w, horn.ι_ι_assoc]
      obtain ⟨g, hg, hgp, _⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration.mem (p := p) |>.2 x b he
      refine CommSq.HasLift.mk' {
        l := g
        fac_left := ?_
        fac_right := hgp }
      apply horn.hom_ext'
      intro j hj
      fin_cases j
      · exact (hj rfl).elim
      · rw [horn.ι_ι_assoc]
        change stdSimplex.δ 1 ≫ g = _
        exact hg.trans (SSet.yonedaEquiv.symm_apply_apply _)
    | succ n =>
      by_cases hi : i = 0
      · subst i
        constructor
        intro a b sq
        exact h _ n a b rfl sq
      · exact InnerFibration.mem (q := p) _
          (innerHornInclusions.intro i (lt_of_le_of_ne (Fin.zero_le _) (Ne.symm hi)) hn)

/-- 概要：left fibration は全辺が cocartesian な cocartesian fibration と同値。
方針：既存の接続と全辺からのホーン充填を組み合わせる。
規約：選択した lift を追加のデータとして保持しない。
使われ方：Kerodon Proposition 5.1.4.15（Tag 01UM）、A2d と F1a の定義の互換性。 -/
lemma leftFibration_iff_cocartesianFibration_all_edges {X B : SSet.{u}} (p : X ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p ∧ ∀ e : X _⦋1⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge p e := by
  constructor
  · intro hp
    have := hp
    exact ⟨inferInstance, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCocartesianEdge_of_leftFibration p⟩
  · rintro ⟨hp, he⟩
    have := hp
    exact leftFibration_of_cocartesianFibration_of_all_edges p he

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
