module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FiniteRelativeOverHom
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallInternalHomContinuity

/-!
概要：μ-small な始域を持つ底上の全相対 Hom は μ-filtered な通常の余極限を保つ。
方針：始域の通常の表示性を底上へ移し、パラメータ付き Hom の各次数を評価する。
規約：非可算正則 μ を要求し、有限始域や底の小ささに置き換えない。
使われ方：引き戻しの小さい図式の compact 同期に必要な相対因子化。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：全空間が μ-presentable な底上の対象も同じ濃度で presentable。
方針：忘却後の因子化と等式の検出を元の底上の射へ戻す。
規約：始域の表示性を明示し、底には条件を課さない。
使われ方：パラメータ付き相対 Hom の通常の連続性。 -/
lemma overMk_isCardinalPresentable_of_left {μ : Cardinal.{u}} [Fact μ.IsRegular]
    {A B : SSet.{u}} (a : A ⟶ B) [IsCardinalPresentable A μ] :
    IsCardinalPresentable (Over.mk a) μ := by
  apply IsCardinalPresentable.mk
  intro J _ _ F c hc
  have : IsFiltered J := isFiltered_of_isCardinalFiltered J μ
  let hc' := isColimitOfPreserves (Over.forget B) hc
  constructor
  · intro g
    obtain ⟨j, f, hf⟩ := IsCardinalPresentable.exists_hom_of_isColimit (X := A) μ hc' g.left
    change f ≫ (c.ι.app j).left = g.left at hf
    have hb : f ≫ (F.obj j).hom = a := by
      calc
        f ≫ (F.obj j).hom = f ≫ ((c.ι.app j).left ≫ c.pt.hom) :=
          congrArg (fun k ↦ f ≫ k) (c.ι.app j).w.symm
        _ = (f ≫ (c.ι.app j).left) ≫ c.pt.hom := (Category.assoc _ _ _).symm
        _ = g.left ≫ c.pt.hom := congrArg (fun k ↦ k ≫ c.pt.hom) hf
        _ = a := g.w
    exact ⟨j, Over.homMk f hb, Over.OverMorphism.ext hf⟩
  · intro j f g h
    obtain ⟨j', t, ht⟩ := IsCardinalPresentable.exists_eq_of_isColimit' (X := A) μ
      hc' f.left g.left (congrArg (fun k ↦ k.left) h)
    exact ⟨j', t, Over.OverMorphism.ext ht⟩

/-- 概要：μ-small な始域の相対 Hom 関手は同じ μ-filtered 余極限を保存する。
方針：各次数を μ-small な始域と標準単体の積からの底上 Hom と自然に比較する。
規約：元の始域の底への射と全パラメータを保持する。
使われ方：一般 coherent 相対 Hom 保存へ移す通常の入力。 -/
lemma smallRelativeOverHom_preservesCardinalFilteredColimits
    {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    {B : SSet.{u}} (A : Over B) (hA : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall μ A.left)
    (J : Type u) [SmallCategory J] [IsCardinalFiltered J μ] :
    PreservesColimitsOfShape J (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.relativeOverHomFunctor A) := by
  apply preservesColimitsOfShape_of_evaluation
  intro n
  have hn : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall μ (A.left ⊗ stdSimplex.obj n.unop) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isKappaSmall_tensor hμ hA (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.isKappaSmall_of_finite hμ.le _)
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallShape_isCardinalPresentable hμ (A.left ⊗ stdSimplex.obj n.unop) hn
  have : IsCardinalPresentable (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.overTensorParameter A (stdSimplex.obj n.unop)) μ :=
    overMk_isCardinalPresentable_of_left _
  have : PreservesColimitsOfShape J
      (coyoneda.obj (Opposite.op (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.overTensorParameter A (stdSimplex.obj n.unop)))) :=
    preservesColimitsOfShape_of_isCardinalPresentable _ μ J
  exact preservesColimitsOfShape_of_natIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.relativeOverHomEvaluationIso A n).symm

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
