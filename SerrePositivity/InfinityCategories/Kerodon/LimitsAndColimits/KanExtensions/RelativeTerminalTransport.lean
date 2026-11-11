module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeLimit

/-!
概要：相対始対象と終対象の双対性、および同型な可換正方形による終対象条件の移送。
方針：二重反転の標準同型と指定 pinched 比較の自然性を使う。
規約：単なる h 圏の対象条件へ弱めない。
使われ方：相対余極限余錐の反転を標準相対極限として判定する。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：単体集合の同型は各次数で全射。
方針：逆同型の像を逆像とする。
規約：頂点の次数を含め任意の次数で使える。
使われ方：相対頂点条件の同型による移送の全射性。 -/
lemma kanIso_app_surjective {A B : SSet.{u}} (e : A ≅ B) (n : SimplexCategoryᵒᵖ) :
    Function.Surjective (e.hom.app n) := by
  intro y
  refine ⟨e.inv.app n y, ?_⟩
  change (e.inv ≫ e.hom).app n y = y
  rw [Iso.inv_hom_id]
  rfl

/-- 概要：U に関する相対始対象性は反転した U に関する相対終対象性と同値。
方針：定義を二度反転し、二重反転の標準同型の自然性で戻す。
規約：U 自身の充填性は要求しない。
使われ方：相対余極限と相対極限の双対性。 -/
lemma kanRelativeInitialVertex_iff_terminal_op {D E : SSet.{u}}
    [Quasicategory D] [Quasicategory E] (U : D ⟶ E) (x : D _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.KanRelativeInitialVertex U x ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.KanRelativeTerminalVertex (SSet.opFunctor.map U) (SSet.opObjEquiv.symm x) := by
  have : Quasicategory ((SSet.opFunctor ⋙ SSet.opFunctor).obj D) :=
    inferInstanceAs (Quasicategory D.op.op)
  have : Quasicategory ((SSet.opFunctor ⋙ SSet.opFunctor).obj E) :=
    inferInstanceAs (Quasicategory E.op.op)
  have : Quasicategory ((𝟭 SSet.{u}).obj D) := inferInstanceAs (Quasicategory D)
  have : Quasicategory ((𝟭 SSet.{u}).obj E) := inferInstanceAs (Quasicategory E)
  let a := SSet.opFunctorCompOpFunctorIso.app D
  let b := SSet.opFunctorCompOpFunctorIso.app E
  have hn : a.hom ≫ U = SSet.opFunctor.map (SSet.opFunctor.map U) ≫ b.hom :=
    (SSet.opFunctorCompOpFunctorIso.hom.naturality U).symm
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeInitialVertex_iff_of_comparison
    (SSet.opFunctor.map (SSet.opFunctor.map U)) U a.hom b.hom hn
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso a).isQCatEquivalence.isFullyFaithful
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso b).isQCatEquivalence.isFullyFaithful
    (kanIso_app_surjective a (Opposite.op ⦋0⦌))
    (SSet.opObjEquiv.symm (SSet.opObjEquiv.symm x))
  exact h.symm

/-- 概要：同型な可換正方形は相対終対象性を保ち反映する。
方針：正方形を反転し、相対始対象性の充満忠実比較を適用する。
規約：両側の比較に厳密な単体集合の同型を使う。
使われ方：slice と反転 coslice の同型に相対極限条件を移す。 -/
lemma kanRelativeTerminalVertex_iff_of_iso_square {A B C D : SSet.{u}}
    [Quasicategory A] [Quasicategory B] [Quasicategory C] [Quasicategory D]
    (f : A ⟶ B) (g : C ⟶ D) (a : A ≅ C) (b : B ≅ D)
    (h : a.hom ≫ g = f ≫ b.hom) (x : A _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.KanRelativeTerminalVertex f x ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.KanRelativeTerminalVertex g (a.hom.app (Opposite.op ⦋0⦌) x) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeInitialVertex_iff_of_comparison
    (SSet.opFunctor.map f) (SSet.opFunctor.map g)
    (SSet.opFunctor.map a.hom) (SSet.opFunctor.map b.hom)
    (by rw [← Functor.map_comp, h, Functor.map_comp])
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (SSet.opFunctor.mapIso a)).isQCatEquivalence.isFullyFaithful
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (SSet.opFunctor.mapIso b)).isQCatEquivalence.isFullyFaithful
  exact kanIso_app_surjective (SSet.opFunctor.mapIso a) (Opposite.op ⦋0⦌)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
