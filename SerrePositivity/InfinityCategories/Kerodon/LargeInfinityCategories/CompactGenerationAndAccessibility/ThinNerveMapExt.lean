module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.OrdinalPrefixes

/-!
概要：thin 圏の nerve への全図式の等式を、元の頂点上で判定する。
方針：自然性で任意単体の各頂点を零単体へ制限し、thin 性で全射を回収する。
規約：一般の quasicategory を対象とする主張には使わない。
使われ方：一頂点追加の順序形状の厳密な可換性。

対応節は Kerodon 9.4（Tag 06GT）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility

/-- 概要：thin nerve への二つの射は零単体上で一致すれば全単体上で一致する。
方針：任意単体の各頂点への自然性と thin 圏の全単体判定を使う。
規約：対象圏の thin 性を明示する。
使われ方：元の順序形状の比較等式。 -/
lemma hom_into_thinNerve_ext {X : SSet.{u}} {I : Type u}
    [SmallCategory I] [Quiver.IsThin I] {f g : X ⟶ nerve I}
    (h : f.app (Opposite.op ⦋0⦌) = g.app (Opposite.op ⦋0⦌)) : f = g := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  refine ComposableArrows.ext (fun i ↦ ?_) (fun _ _ ↦ Subsingleton.elim _ _)
  let θ : ⦋0⦌ ⟶ n.unop := SimplexCategory.mkHom (OrderHom.const _ i)
  have hf := congrArg (fun t ↦ (t s).obj 0) (f.naturality θ.op)
  have hg := congrArg (fun t ↦ (t s).obj 0) (g.naturality θ.op)
  change (f.app (Opposite.op ⦋0⦌) (X.map θ.op s)).obj 0 = (f.app n s).obj i at hf
  change (g.app (Opposite.op ⦋0⦌) (X.map θ.op s)).obj 0 = (g.app n s).obj i at hg
  exact hf.symm.trans ((congrArg (fun t ↦ (t (X.map θ.op s)).obj 0) h).trans hg)

/-- 概要：join の各頂点は元の左または右因子から来る。
方針：零次元の join の切断位置を二通りに分ける。
規約：各因子の元の零単体を回収する。
使われ方：thin nerve への join 図式の等号判定。 -/
lemma join_vertex_cases {A B : SSet.{u}} (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A B) _⦋0⦌) :
    (∃ a, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A B).app (Opposite.op ⦋0⦌) a = v) ∨
      ∃ b, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A B).app (Opposite.op ⦋0⦌) b = v := by
  rcases v with ⟨k, a, b⟩
  fin_cases k
  · right
    cases a
    exact ⟨b, rfl⟩
  · left
    cases b
    exact ⟨a, rfl⟩

/-- 概要：thin nerve への join の二つの射は、両因子への制限が一致すれば一致する。
方針：両因子が全頂点を覆うことを全単体判定へ渡す。
規約：対象は明示された thin 圏の nerve。
使われ方：閉前置段への一頂点追加の二つの順序形状比較。 -/
lemma join_hom_into_thinNerve_ext {A B : SSet.{u}} {I : Type u}
    [SmallCategory I] [Quiver.IsThin I] {f g : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A B ⟶ nerve I}
    (hl : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A B ≫ f = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A B ≫ g)
    (hr : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A B ≫ f = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A B ≫ g) : f = g := by
  apply hom_into_thinNerve_ext
  apply ConcreteCategory.hom_ext
  intro v
  rcases join_vertex_cases v with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · exact congrArg (fun t ↦ t.app (Opposite.op ⦋0⦌) a) hl
  · exact congrArg (fun t ↦ t.app (Opposite.op ⦋0⦌) b) hr

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility
