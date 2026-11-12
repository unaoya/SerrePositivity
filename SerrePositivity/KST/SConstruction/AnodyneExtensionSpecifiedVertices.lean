module
public import SerrePositivity.KST.SConstruction.AnodyneExtensionChoices

/-! # 元の指定延長を保つ選択空間の頂点と普遍族
概要：元の具体的な延長を選択空間へ入れ、実際の延長として厳密に回収する。
方針：内部 Hom の頂点と pullback の普遍性を使い、元の全選択の評価族も取り出す。
規約：既に指定された延長を新しいホモトピー代表に選び直さない。
使われ方：既存 K 適合辺を保持する三角形を、可縮な貼り合わせ選択へ含める。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 元の制限式を満たす指定延長を、そのまま全選択空間の頂点へ入れる。 -/
def anodyneExtensionVertex {A B Z : SSet.{u}} (i : A ⟶ B) (h : A ⟶ Z)
    (f : B ⟶ Z) (hf : i ≫ f = h) : (anodyneExtensionChoices i h) _⦋0⦌ := by
  let q : (Δ[0] : SSet.{u}) ⟶ anodyneExtensionChoices i h :=
    pullback.lift (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f)) (𝟙 _) (by
      apply SSet.yonedaEquiv.injective
      rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply, Category.id_comp,
        Equiv.apply_symm_apply]
      change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (i ≫ f) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex h
      rw [hf])
  exact q.app (Opposite.op ⦋0⦌) (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})))

/-- 選択空間から指定頂点を評価すると、元の延長そのものを厳密に回収する。 -/
lemma anodyneExtensionAt_vertex {A B Z : SSet.{u}} (i : A ⟶ B) (h : A ⟶ Z)
    (f : B ⟶ Z) (hf : i ≫ f = h) :
    anodyneExtensionAt i h (anodyneExtensionVertex i h f hf) = f := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv B Z).injective
  rw [anodyneExtensionAt, Equiv.apply_symm_apply, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv_apply]
  dsimp only [anodyneExtensionVertex, anodyneExtensionChoices]
  rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app, pullback.lift_fst,
    SSet.yonedaEquiv_symm_app_id]

/-- 全選択を同時に評価する、元の延長空間の全パラメータの実族。 -/
def anodyneExtensionFamily {A B Z : SSet.{u}} (i : A ⟶ B) (h : A ⟶ Z) :
    B ⊗ anodyneExtensionChoices i h ⟶ Z :=
  uncurry (pullback.fst ((pre i).app Z) (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex h)))

/-- 全選択の実族も、元の指定部分を全パラメータで厳密に回収する。 -/
lemma anodyneExtensionFamily_fac {A B Z : SSet.{u}} (i : A ⟶ B) (h : A ⟶ Z) :
    (i ▷ anodyneExtensionChoices i h) ≫ anodyneExtensionFamily i h =
      fst A (anodyneExtensionChoices i h) ≫ h := by
  rw [anodyneExtensionFamily, ← uncurry_pre_app, pullback.condition]
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨x, v⟩
  rfl

end SerrePositivity.KST.SConstruction
