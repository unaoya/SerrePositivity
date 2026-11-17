module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameElementSpans
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Replacements.SpecialHammock
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ChosenResolutionHom

/-!
# 同じ関手的分解の Hom から特殊な三本矢への全単体の図式

概要：Dwyer–Kan §7 の共通比較へ、既存の cosimplicial 分解の全 Hom を送る。
方針：同じ augmentation の次数ごとの trivial fibration と元の fibrant 置換を使う。
規約：元の chosenResolutionHom と同じ二つの関手的分解を保持する。
使われ方：E2b の Map^h と特殊な hammock の高次比較の入力。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison

open CategoryTheory _root_.HomotopicalAlgebra Opposite
open _root_.SerrePositivity.Reedy _root_.SerrePositivity.HomotopyFunctionComplex

variable {C : Type u} [Category.{v} C] [ModelCategory C]

/-- 概要：元の cofibrant 分解の各次数の augmentation は trivial fibration（Dwyer–Kan §7）。
方針：同じ Reedy trivial fibration の成分の定理を使う。
規約：元の分解や augmentation を変更しない。
使われ方：特殊な三本矢の左脚の供給。 -/
lemma resolutionAugmentation_trivialFibration {X : C}
    (q : CofibrantResolution (C := C) simplex X) (n : SimplexCategory) :
    trivialFibrations C (q.augmentation.app n) :=
  trivialFibration_app simplex q.augmentation q.trivial n

/-- 概要：元の分解の全 Hom 単体を特殊な三本矢へ送る（Dwyer–Kan §7）。
方針：同じ次数の分解の augmentation と指定した右の trivial cofibration を使う。
規約：終域や元の端点に cofibrancy・fibrancy を仮定しない。
使われ方：特殊な hammock の共通図式。 -/
def resolutionSpecialSpanFunctor {X Y Z : C}
    (q : CofibrantResolution (C := C) simplex X) (j : Y ⟶ Z)
    (hj : trivialCofibrations C j) :
    (((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom q.obj).obj Z).Elements)ᵒᵖ ⥤ _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.SpecialHammock X Y :=
  _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.frameElementSpanFunctor (trivialFibrations C) (trivialCofibrations C) q.obj q.augmentation
    (resolutionAugmentation_trivialFibration q) j hj

/-- 概要：同じ fibrant 置換の比較は元の trivial cofibration（Hovey §5）。
方針：元の関手的分解の左射の証明を使う。
規約：元の終対象への分解を保持する。
使われ方：特殊な三本矢の右脚の供給。 -/
lemma fibrantTargetComparison_trivialCofibration
    (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
    (Y : C) : trivialCofibrations C ((fibrantTargetComparison fib).app Y) :=
  fib.hi _

/-- 概要：元の chosenResolutionHom の全単体を同じ特殊な三本矢へ送る（Dwyer–Kan §7）。
方針：同じ二つの関手的分解を一般の全単体比較へ代入する。
規約：元の分解・fibrant 置換・全作用素を保持する。
使われ方：実際の Map^h と hammock の高次比較。 -/
def chosenResolutionSpanFunctor
    (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
    (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
    (X Y : C) :
    ((((chosenResolutionHom cof fib).obj (op X)).obj Y).Elements)ᵒᵖ ⥤ _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.SpecialHammock X Y :=
  resolutionSpecialSpanFunctor ((cosimplicialResolutionFamily cof).atObject X)
    ((fibrantTargetComparison fib).app Y) (fibrantTargetComparison_trivialCofibration fib Y)

end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
