module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.NervePosetUniverse
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallPosetDiagramCodes
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SequentialDiagramFiniteStages
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.UniverseJoinSimplexShapes

/-!
概要：native な小さい可算 nerve の持ち上げと、大きい宇宙の同じ可算 nerve を同定する。
方針：poset nerve の宇宙同型と二重 ULift を除く順序同型を合成する。
規約：すべての有限始区間と共終部分列を全射として保持する。
使われ方：全交互可算図式を native な小余極限の添字へ移す。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories


/-- 概要：可算添字の二重持ち上げを除く順序同型。
方針：二重の down で元の自然数を回収する。
規約：自然数を変更しない。
使われ方：可算 nerve の全宇宙同型。 -/
def sequentialDoubleLiftOrderIso :
    ULift.{u + 1} (ULift.{u} ℕ) ≃o ULift.{u + 1} ℕ where
  toFun n := ULift.up n.down.down
  invFun n := ULift.up (ULift.up n.down)
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

/-- 概要：持ち上げた小さい可算 nerve と大きい宇宙の同じ可算 nerve の全同型。
方針：元の自然数を保つ順序同型で二重 ULift を除く。
規約：全次数の実同型。
使われ方：可算交互表示の native 余極限への接続。 -/
def sequentialNerveUniverseIso :
    (SSet.uliftFunctor.{u + 1, u}).obj (nerve (ULift.{u} ℕ)) ≅
      nerve (ULift.{u + 1} ℕ) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.nervePosetUniverseIso (ULift.{u} ℕ) ≪≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.nerveOrderIso sequentialDoubleLiftOrderIso

/-- 概要：可算 nerve の宇宙同型は任意の単調部分列を保つ。
方針：全単体を表す自然数鎖の各値を計算する。
規約：全射の厳密な可換式。
使われ方：偶数・奇数部分列の native 比較。 -/
lemma sequentialNerveUniverseIso_subsequence (a : ℕ → ℕ) (ha : Monotone a) :
    (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialSubsequenceFunctor.{u} a ha)) ≫
      sequentialNerveUniverseIso.hom =
    sequentialNerveUniverseIso.hom ≫ nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialSubsequenceFunctor.{u + 1} a ha) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  exact ComposableArrows.ext (fun _ ↦ rfl) (fun _ _ ↦ Subsingleton.elim _ _)

/-- 概要：可算 nerve の宇宙同型は全有限始区間を厳密に保つ。
方針：有限鎖の各値を計算する。
規約：標準単体の宇宙同型を含む全射の等式。
使われ方：元の小さい表示添字との有限段比較。 -/
lemma sequentialNerveUniverseIso_initialSimplex (n : ℕ) :
    (SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveInitialSimplex.{u} n) ≫
      sequentialNerveUniverseIso.hom =
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso.{u, u + 1} n).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveInitialSimplex.{u + 1} n := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro s
  exact ComposableArrows.ext (fun _ ↦ rfl) (fun _ _ ↦ Subsingleton.elim _ _)

/-- 概要：native な可算 nerve の持ち上げにおける有限始区間。
方針：小さい全始区間を標準単体の宇宙同型で表示する。
規約：全単体の射。
使われ方：native な可算図式の全有限段での検出。 -/
def nativeSequentialInitialSimplex (n : ℕ) :
    (Δ[n] : SSet.{u + 1}) ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (nerve (ULift.{u} ℕ)) :=
  (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso.{u, u + 1} n).inv ≫
    (SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveInitialSimplex.{u} n)

/-- 概要：native な有限始区間は宇宙比較で同じ大きい始区間になる。
方針：全始区間の宇宙自然性と同型の相殺。
規約：全射の等式。
使われ方：可算交互図式の有限段の回収。 -/
lemma nativeSequentialInitialSimplex_universe (n : ℕ) :
    nativeSequentialInitialSimplex.{u} n ≫ sequentialNerveUniverseIso.hom =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveInitialSimplex.{u + 1} n := by
  rw [nativeSequentialInitialSimplex, Category.assoc, sequentialNerveUniverseIso_initialSimplex,
    Iso.inv_hom_id_assoc]

/-- 概要：native な可算図式の全有限始区間での一致は全図式の一致を与える。
方針：宇宙比較の逆で戻し、同じ可算 nerve の全有限段で検出する。
規約：標的の quasicategory 性は不要。
使われ方：偶数部分列と元の表示図式の全比較。 -/
lemma nativeSequential_hom_ext {X : SSet.{u + 1}}
    {F G : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (ULift.{u} ℕ)) ⟶ X}
    (h : ∀ n, nativeSequentialInitialSimplex n ≫ F = nativeSequentialInitialSimplex n ≫ G) :
    F = G := by
  apply (cancel_epi sequentialNerveUniverseIso.inv).mp
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerve_hom_ext_initialSimplex
  intro n
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveInitialSimplex.{u + 1} (n + 1) ≫ sequentialNerveUniverseIso.inv =
      nativeSequentialInitialSimplex (n + 1) := by
    rw [← nativeSequentialInitialSimplex_universe, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  simpa only [← Category.assoc, he] using h (n + 1)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
