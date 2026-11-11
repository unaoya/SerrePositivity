module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitCommaFunctorSquare
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorTriangleSquare

/-!
概要：関手正方形を comma の二重区間の coherence へ戻す。
方針：curry を戻し、パラメータと二つの区間の並べ替えを逆にする。
規約：四辺の代表を厳密に回収する。
使われ方：導来 fiber から comma の族への復元。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Diagrams

/-- 概要：comma の正方形のパラメータの並べ替えを逆に戻す。
方針：最初の二因子を交換して結合子でまとめる。
規約：入力は (射の区間×A)×coherence の区間。
使われ方：関手正方形の uncurry の入力を作る。 -/
def commaSquareUnreorder (A : SSet.{u}) :
    ((Δ[1] : SSet.{u}) ⊗ A) ⊗ Δ[1] ⟶ A ⊗ ((Δ[1] : SSet.{u}) ⊗ Δ[1]) :=
  ((β_ (Δ[1] : SSet.{u}) A).hom ▷ Δ[1]) ≫ (α_ A Δ[1] Δ[1]).hom

/-- 概要：並べ替えて逆に戻すと恒等。
方針：積の三成分を計算する。
規約：厳密な射の等式。
使われ方：coherence の復元の整合性。 -/
lemma commaSquareReorder_unreorder (A : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.commaSquareReorder A ≫ commaSquareUnreorder A = 𝟙 _ := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro a
  rfl

/-- 概要：逆に並べ替えて戻しても恒等。
方針：積の三成分を計算する。
規約：厳密な射の等式。
使われ方：関手正方形の回収。 -/
lemma commaSquareUnreorder_reorder (A : SSet.{u}) :
    commaSquareUnreorder A ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.commaSquareReorder A = 𝟙 _ := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro a
  rfl

/-- 概要：coherence の時間零は関手正方形の下辺へ移る。
方針：積の成分で時刻零を計算する。
規約：射の区間と時間の区間を区別する。
使われ方：coherence の始点条件。 -/
lemma commaSquareUnreorder_zero (A : SSet.{u}) :
    SSet.ι₀ ≫ commaSquareUnreorder A =
      (β_ (Δ[1] : SSet.{u}) A).hom ≫ A ◁
        (SSet.ι₀ : (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1]) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro a
  rfl

/-- 概要：coherence の時間一は関手正方形の上辺へ移る。
方針：積の成分で時刻一を計算する。
規約：射の区間と時間の区間を区別する。
使われ方：coherence の終点条件。 -/
lemma commaSquareUnreorder_one (A : SSet.{u}) :
    SSet.ι₁ ≫ commaSquareUnreorder A =
      (β_ (Δ[1] : SSet.{u}) A).hom ≫ A ◁
        (SSet.ι₁ : (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1]) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro a
  rfl

/-- 概要：射の区間の指定端点は関手正方形の対応する縦辺へ移る。
方針：時刻を保って射の区間だけを固定する。
規約：端点 i は任意。
使われ方：comma の二側辺の復元。 -/
lemma commaSquareUnreorder_endpoint (A : SSet.{u}) (i : Fin 2) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i A ▷ (Δ[1] : SSet.{u})) ≫ commaSquareUnreorder A =
      A ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i (Δ[1] : SSet.{u}) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro a
  rfl

/-- 概要：下辺が定値関手 x の恒等である関手正方形を coherence のホモトピーに戻す。
方針：正方形を uncurry し、時間の両端を四辺の公式で計算する。
規約：三辺のホモトピーの代表は変更しない。
使われ方：comma の族の復元の coherence 成分。 -/
noncomputable def functorSquareCoherence {A X : SSet.{u}} {x : X _⦋0⦌} {V W : A ⟶ X}
    {l : SSet.Homotopy (SSet.const x) V} {r : SSet.Homotopy V W}
    {d : SSet.Homotopy (SSet.const x) W} (Q : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionSquare l r d) :
    SSet.Homotopy (SSet.const x : (Δ[1] : SSet.{u}) ⊗ A ⟶ X)
      ((β_ (Δ[1] : SSet.{u}) A).hom ≫ r.h) where
  h := commaSquareUnreorder A ≫ uncurry Q.diagram
  h₀ := by
    rw [← Category.assoc, commaSquareUnreorder_zero, Category.assoc,
      ← uncurry_natural_left, Q.bottom, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.uncurry_const_functorVertex]
    change (β_ (Δ[1] : SSet.{u}) A).hom ≫ _ ≫ SSet.const x = SSet.const x
    rw [SSet.comp_const, SSet.comp_const]
  h₁ := by
    rw [← Category.assoc, commaSquareUnreorder_one, Category.assoc,
      ← uncurry_natural_left, Q.top, uncurry_curry]
    rfl
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro a
    exact False.elim a.1.property

/-- 概要：復元した coherence の零側辺は元の左辺のホモトピー。
方針：逆並べ替えの端点公式と uncurry の自然性を使う。
規約：raw な射の厳密な等式。
使われ方：単位の代表を保持する。 -/
lemma functorSquareCoherence_left {A X : SSet.{u}} {x : X _⦋0⦌} {V W : A ⟶ X}
    {l : SSet.Homotopy (SSet.const x) V} {r : SSet.Homotopy V W}
    {d : SSet.Homotopy (SSet.const x) W} (Q : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionSquare l r d) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ▷ (Δ[1] : SSet.{u})) ≫ (functorSquareCoherence Q).h = l.h := by
  change _ ≫ (commaSquareUnreorder A ≫ uncurry Q.diagram) = _
  rw [← Category.assoc, commaSquareUnreorder_endpoint, ← uncurry_natural_left,
    Q.left, uncurry_curry]

/-- 概要：復元した coherence の一側辺は元の右辺のホモトピー。
方針：逆並べ替えの端点公式と uncurry の自然性を使う。
規約：raw な射の厳密な等式。
使われ方：指定した終辺の代表を保持する。 -/
lemma functorSquareCoherence_right {A X : SSet.{u}} {x : X _⦋0⦌} {V W : A ⟶ X}
    {l : SSet.Homotopy (SSet.const x) V} {r : SSet.Homotopy V W}
    {d : SSet.Homotopy (SSet.const x) W} (Q : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionSquare l r d) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ▷ (Δ[1] : SSet.{u})) ≫ (functorSquareCoherence Q).h = d.h := by
  change _ ≫ (commaSquareUnreorder A ≫ uncurry Q.diagram) = _
  rw [← Category.assoc, commaSquareUnreorder_endpoint, ← uncurry_natural_left,
    Q.right, uncurry_curry]

/-- 概要：復元した coherence を再び curry すると元の関手正方形。
方針：並べ替えと逆並べ替え、curry と uncurry の両逆を消去する。
規約：四辺だけでなく図式自体の厳密な等式。
使われ方：正方形の復元で coherence の情報を失わないことの検証。 -/
lemma functorSquareCoherence_recover {A X : SSet.{u}} {x : X _⦋0⦌} {V W : A ⟶ X}
    {l : SSet.Homotopy (SSet.const x) V} {r : SSet.Homotopy V W}
    {d : SSet.Homotopy (SSet.const x) W} (Q : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionSquare l r d) :
    curry (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.commaSquareReorder A ≫ (functorSquareCoherence Q).h) = Q.diagram := by
  change curry (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.commaSquareReorder A ≫ (commaSquareUnreorder A ≫ uncurry Q.diagram)) = _
  rw [← Category.assoc, commaSquareReorder_unreorder, Category.id_comp, curry_uncurry]

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Diagrams
