module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroTriangleHoMap
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Definition

/-! # 任意のホモトピー圏の射を含む fiber と cofiber の短複体

概要：安定 ∞ 圏の h C の全ての射は cofiber 短複体の第一射、fiber 短複体の第二射として現れる。
方針：射を実際の辺で表し、安定性による普遍四角形を選び、Arrow で元の射と比較する。
規約：短複体の存在まで。接続射と三角圏の公理は別途証明する。
使われ方：S4 の TR1 の構成の入力と S5 の fiber 列。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：h C の任意の射を第一射に持つ cofiber 短複体が存在する。
方針：辺による射の表示に cofiber 四角形を選び、端点も含めて Arrow で照合する。
規約：安定性を仮定し、接続射の存在はまだ主張しない。
使われ方：S4 の distinguished triangle の存在の最初の段階。 -/
lemma exists_cofiber_hoShortComplex {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    {a b : hoFunctor.obj X} (f : a ⟶ b) :
    ∃ t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsCofiberSequence t ∧ Arrow.mk t.hoShortComplex.f = Arrow.mk f := by
  obtain ⟨x, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective a
  obtain ⟨y, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective b
  obtain ⟨e, he⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective x y f
  let s := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.chosenCofiberSquare e
  refine ⟨s.toZeroTriangle, s.isPushout, s.hoShortComplex_f_arrow.trans ?_⟩
  exact congrArg Arrow.mk he

/-- 概要：h C の任意の射を第二射に持つ fiber 短複体が存在する。
方針：辺の表示に fiber 四角形を選び、指定された右辺の類を比較する。
規約：安定性の fiber 存在条件を使う。使われ方：S5 の任意の射の fiber 列。 -/
lemma exists_fiber_hoShortComplex {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    {a b : hoFunctor.obj X} (f : a ⟶ b) :
    ∃ t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsFiberSequence t ∧ Arrow.mk t.hoShortComplex.g = Arrow.mk f := by
  obtain ⟨x, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective a
  obtain ⟨y, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective b
  obtain ⟨e, he⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective x y f
  let s := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.chosenFiberSquare e
  refine ⟨s.toZeroTriangle, s.isPullback, s.hoShortComplex_g_arrow.trans ?_⟩
  exact congrArg Arrow.mk he

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
