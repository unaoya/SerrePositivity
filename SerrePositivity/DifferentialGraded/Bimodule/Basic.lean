module
public import SerrePositivity.DifferentialGraded.Module.LeftAction
public import SerrePositivity.DifferentialGraded.Module.HomElements
public import SerrePositivity.DifferentialGraded.Module.Category

/-! # 右B・左C dg bimodule

Cから右B加群の全Hom end豊穣圏へのdg関手を使う。
左C作用は最初から全dg自然な右B加群間のHomに値を持ち、閉零自然性では代用しない。
積dg圏とのuncurrying比較は後続の工程。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite CochainComplex HomComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B]

/-- 右B・左Cの全dg自然なbimodule。 -/
def Bimodule := DGFunctor A C (RightModule A B)

namespace Bimodule
variable {A B C}

/-- 右B加群への豊穣関手として読む。 -/
abbrev toFunctor (M : Bimodule A B C) : DGFunctor A C (RightModule A B) := M

/-- Cの対象を固定した右B加群。 -/
abbrev rightAt (M : Bimodule A B C) (c : C) : RightModule A B := M.toFunctor.obj c

/-- Bの対象を固定した左C加群。 -/
def leftAt (M : Bimodule A B C) (b : B) : LeftModule A C :=
  M.toFunctor.comp (moduleEvaluationDG A B b)

/-- 両対象での値。 -/
abbrev value (M : Bimodule A B C) (b : B) (c : C) : Complex A :=
  (M.rightAt c).obj (op b)

/-- 左C作用の全次数cochain。 -/
def leftCochain (M : Bimodule A B C) {c c' : C} {q : ℤ}
    (g : GradedHom A c c' q) (b : B) :
    Cochain (M.value b c) (M.value b c') q :=
  (moduleHomπ A B (M.rightAt c) (M.rightAt c') b).f q ((M.toFunctor.map c c').f q g)

/-- 二つの作用の交換は全Hom endの自然性そのもの。 -/
lemma interchange (M : Bimodule A B C) {b b' : B} {c c' : C} {p q : ℤ}
    (f : GradedHom A (op b') (op b) p) (g : GradedHom A c c' q) :
    (((M.rightAt c).map (op b') (op b)).f p f).comp (M.leftCochain g b)
        (by omega : p + q = q + p) =
      (q * p).negOnePow • ((M.leftCochain g b').comp
        (((M.rightAt c').map (op b') (op b)).f p f) rfl) :=
  moduleHomElement_naturality A B q ((M.toFunctor.map c c').f q g) (op b') (op b) p f

/-- 左cochainは評価によって得た左加群の作用と一致する。 -/
lemma leftCochain_eq (M : Bimodule A B C) {c c' : C} {q : ℤ}
    (g : GradedHom A c c' q) (b : B) :
    M.leftCochain g b = ((M.leftAt b).map c c').f q g := rfl

end Bimodule
end SerrePositivity.DifferentialGraded
