module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FunctorIsoCurryComposition
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.JointComparisonComposition

/-!
概要：共同比較の合成を、元の図式値の指定実現同型の合成へ移す。
方針：curry 後の端点等式を明示し、元の共同三角形の同型の合成を移送する。
規約：構成済みの realizationIso そのものを比較する。
使われ方：P-12 の共同切断底変換の実現の合成則。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：指定関手同型を元の二つの図式等式で移送する。
方針：両端の頂点等式の同型を合成する。
規約：元の同型を保持する。使われ方：共同比較実現の端点正規化。 -/
def diagramIsoCongr {A X : SSet.{u}} {f g f' g' : A ⟶ X}
    (hf : f = f') (hg : g = g') (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f' g' :=
  (eqToIso (congrArg (fun h ↦ HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex h)) hf)).symm ≪≫ e ≪≫
    eqToIso (congrArg (fun h ↦ HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex h)) hg)

/-- 概要：図式等式で移送した同型は元の同型と異種等式で一致する。
方針：端点等式を消去し恒等同型を除く。
規約：元の指定同型を使う。使われ方：実現同型の定義中の型移送との照合。 -/
lemma diagramIsoCongr_heq {A X : SSet.{u}} {f g f' g' : A ⟶ X}
    (hf : f = f') (hg : g = g') (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) :
    HEq (diagramIsoCongr hf hg e) e := by
  subst f' g'
  simp only [diagramIsoCongr, eqToIso_refl, Iso.refl_symm, Iso.refl_trans, Iso.trans_refl]
  rfl

/-- 概要：同じ中間図式での同型移送は元の合成を保存する。
方針：三つの端点等式を消去する。
規約：同じ中間等式を使う。使われ方：指定実現同型の合成の正規化。 -/
lemma diagramIsoCongr_trans {A X : SSet.{u}} {f g h f' g' h' : A ⟶ X}
    (hf : f = f') (hg : g = g') (hh : h = h') (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso g h) :
    diagramIsoCongr hf hh (e ≪≫ d) = diagramIsoCongr hf hg e ≪≫ diagramIsoCongr hg hh d := by
  subst f' g' h'
  simp only [diagramIsoCongr, eqToIso_refl, Iso.refl_symm, Iso.refl_trans, Iso.trans_refl]

/-- 概要：共同評価を curry すると元の図式値実現となる。
方針：内部 Hom の curry の前合成公式を使う。
規約：元の全図式を保持する。使われ方：共同比較を実現した両端の正規化。 -/
lemma jointEvaluation_curry {C : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
    {J : Type u} [Category.{u} J] (D : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagram C J) :
    curry D.jointEvaluation = D.realization :=
  curry_natural_left _ _

/-- 概要：指定された図式比較の実現は、元の共同比較の curry の型移送である。
方針：実現同型の定義中の端点書き換えを異種等式へ戻す。
規約：元の実現同型を保持する。使われ方：図式値の合成式の正規化。 -/
lemma jointRealizationIso_heq_curry
    {C : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
    {J : Type u} [Category.{u} J] {D E : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagram C J}
    (η : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagramComparison D E)
    (hη : ∀ j (p : C), _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence
      (X := ((D.obj j).obj p).obj) (Y := ((E.obj j).obj p).obj) ((η.component j).val p)) :
    HEq (η.realizationIso hη) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorIso.curry (η.jointComparisonIso hη)) := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagramComparison.realizationIso
  dsimp only [_root_.id]
  have hcast {T U : Sort (u + 2)} (h : T = U) (z : T) : HEq (Eq.mp h z) z := by
    cases h
    rfl
  exact hcast _ _

/-- 概要：指定実現同型を元の共同比較の curry の正規化として表示する。
方針：二つの表示を同じ未正規化の同型との異種等式で比較する。
規約：元の指定比較を変更しない。使われ方：実現比較の合成則への接続。 -/
lemma jointRealizationIso_normalized
    {C : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
    {J : Type u} [Category.{u} J] {D E : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagram C J}
    (η : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagramComparison D E)
    (hη : ∀ j (p : C), _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence
      (X := ((D.obj j).obj p).obj) (Y := ((E.obj j).obj p).obj) ((η.component j).val p)) :
    η.realizationIso hη = diagramIsoCongr (jointEvaluation_curry D) (jointEvaluation_curry E)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorIso.curry (η.jointComparisonIso hη)) :=
  eq_of_heq ((jointRealizationIso_heq_curry η hη).trans
    (diagramIsoCongr_heq (jointEvaluation_curry D) (jointEvaluation_curry E)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorIso.curry (η.jointComparisonIso hη))).symm)

/-- 概要：指定された図式値の比較実現は、全自然な同型の合成を保存する。
方針：共同比較の三角形、curry の合成保存、端点移送の合成則を使う。
規約：既存の realizationIso そのものの等式。
使われ方：P-12 の切断底変換比較の合成を全図式で検証する。 -/
lemma jointRealizationIso_trans
    {C : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
    {J : Type u} [Category.{u} J] {D E H : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagram C J}
    (η : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagramComparison D E) (θ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagramComparison E H)
    (hη : ∀ j (p : C), _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence
      (X := ((D.obj j).obj p).obj) (Y := ((E.obj j).obj p).obj) ((η.component j).val p))
    (hθ : ∀ j (p : C), _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence
      (X := ((E.obj j).obj p).obj) (Y := ((H.obj j).obj p).obj) ((θ.component j).val p))
    (hηθ : ∀ j (p : C), _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence
      (X := ((D.obj j).obj p).obj) (Y := ((H.obj j).obj p).obj)
        (((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.jointComparisonTrans η θ).component j).val p)) :
    η.realizationIso hη ≪≫ θ.realizationIso hθ =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.jointComparisonTrans η θ).realizationIso hηθ := by
  rw [jointRealizationIso_normalized η, jointRealizationIso_normalized θ,
    jointRealizationIso_normalized (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.jointComparisonTrans η θ), ← diagramIsoCongr_trans,
    ← _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorIsoCurry_trans, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.jointComparisonIso_trans η θ hη hθ hηθ]

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
