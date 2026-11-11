module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConstantFunctor
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.EnrichedPostcomposition

/-!
概要：定値関手間の adjunct 対応の対象変数に関する自然性。
方針：二胞体の whisker を内部 Hom の作用へ移し、定値関手の合成の輸送を補う。
規約：対象変数の射はホモトピー圏の任意の射。
使われ方：Kerodon Prop 6.2.1.17（Tag 02F1） の写像空間の自然性。

対応節は Kerodon 6.2（Tag 02EH）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Bicategory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories

/-- 概要：adjunct は h Fun の任意の射による後合成に自然。
方針：二胞体の表示同値の全射性と右 whisker の比較を使う。
規約：U,V,V' は任意の関手。
使われ方：定値関手間の Hom の終域変数自然性。 -/
lemma homEquiv_comp_right {A X Y : SSet.{u}}
    [Quasicategory A] [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction F G)
    (U : A ⟶ X) (V V' : A ⟶ Y)
    (α : (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (U ≫ F)) : hoFunctor.obj ((ihom A).obj Y)) ⟶
      HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex V))
    (β : (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex V) : hoFunctor.obj ((ihom A).obj Y)) ⟶
      HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex V')) :
    a.homEquiv U V' (α ≫ β) = a.homEquiv U V α ≫
      (hoFunctor.map ((ihom A).map G)).toFunctor.map β := by
  obtain ⟨α', rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv (U ≫ F) V).surjective α
  obtain ⟨β', rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv V V').surjective β
  have h := a.homEquiv_naturality_right U V V' α' β'
  exact h.trans (congrArg (a.homEquiv U V (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv _ _ α') ≫ ·)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCell_whiskerRight (U := V) (V := V') β' G))

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories (homEquiv_comp_right)


/-- 概要：adjunct は h Fun の任意の射による前合成に自然。
方針：二胞体の表示同値の全射性と右 whisker の比較を使う。
規約：U',U,V は任意の関手。
使われ方：定値関手間の Hom の始域変数自然性。 -/
lemma homEquiv_comp_left {A X Y : SSet.{u}}
    [Quasicategory A] [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction F G)
    (U U' : A ⟶ X) (V : A ⟶ Y)
    (γ : (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex U') : hoFunctor.obj ((ihom A).obj X)) ⟶
      HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex U))
    (α : (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (U ≫ F)) : hoFunctor.obj ((ihom A).obj Y)) ⟶
      HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex V)) :
    a.homEquiv U' V ((hoFunctor.map ((ihom A).map F)).toFunctor.map γ ≫ α) =
      γ ≫ a.homEquiv U V α := by
  obtain ⟨γ', rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv U' U).surjective γ
  obtain ⟨α', rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv (U ≫ F) V).surjective α
  have h := a.homEquiv_naturality_left U U' V γ' α'
  have hw : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv (U' ≫ F) (U ≫ F) (γ' ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap F) =
      (hoFunctor.map ((ihom A).map F)).toFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv U' U γ') :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCell_whiskerRight (U := U') (V := U) γ' F
  exact (congrArg (fun t ↦ a.homEquiv U' V (t ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv (U ≫ F) V α'))
    hw.symm).trans h

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories (homEquiv_comp_left)


/-- 概要：定値関手間の adjunct は終域のホモトピー圏の射に自然。
方針：一般の自然性と定値二胞体の後合成の公式の輸送を相殺する。
規約：パラメータ A は quasicategory。
使われ方：写像空間の比較の後合成との可換性。 -/
lemma constantHomEquiv_naturality_right {A X Y : SSet.{u}}
    [Quasicategory A] [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction F G)
    (x : X _⦋0⦌) {y y' : Y _⦋0⦌}
    (α : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.ConstantFunctorHom A Y (F.app (Opposite.op ⦋0⦌) x) y)
    (δ : (HomotopyCategory.mk y : hoFunctor.obj Y) ⟶ HomotopyCategory.mk y') :
    a.constantHomEquiv A x y' (α ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap A δ) =
      a.constantHomEquiv A x y α ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap A ((hoFunctor.map G).toFunctor.map δ) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction.constantHomEquiv, Equiv.trans_apply, Iso.homCongr_apply,
    Iso.symm_inv, Iso.refl_hom, Iso.refl_inv, Category.id_comp, Category.comp_id]
  rw [← Category.assoc, homEquiv_comp_right]
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap_postcomp A G δ]
  simp [Category.assoc]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories (constantHomEquiv_naturality_right)


/-- 概要：定値関手間の adjunct は始域のホモトピー圏の射に自然。
方針：定値二胞体の後合成を展開し、一般の前合成自然性を適用する。
規約：パラメータ A は quasicategory。
使われ方：写像空間の比較の前合成との可換性。 -/
lemma constantHomEquiv_naturality_left {A X Y : SSet.{u}}
    [Quasicategory A] [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction F G)
    {x' x : X _⦋0⦌} (y : Y _⦋0⦌)
    (γ : (HomotopyCategory.mk x' : hoFunctor.obj X) ⟶ HomotopyCategory.mk x)
    (α : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.ConstantFunctorHom A Y (F.app (Opposite.op ⦋0⦌) x) y) :
    a.constantHomEquiv A x' y
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap A ((hoFunctor.map F).toFunctor.map γ) ≫ α) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap A γ ≫ a.constantHomEquiv A x y α := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap_postcomp A F γ]
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction.constantHomEquiv, Equiv.trans_apply, Iso.homCongr_apply,
    Iso.symm_inv, Iso.refl_hom, Iso.refl_inv, Category.id_comp, Category.comp_id]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [homEquiv_comp_left]
  simp only [Category.assoc]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories (constantHomEquiv_naturality_left)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
