module

public import SerrePositivity.KST.Comparison.FreeDegeneraciesCalculations
public import Mathlib.CategoryTheory.Limits.Types.Coproducts

/-!
# 自由な退化の次数ごとの全射の添字

概要：全射の形を元の単体から分離し、各次数を評価関手の直和で表示する準備をする。
方針：標準形の中間対象と全射を独立な添字にまとめる。
規約：Segal 1974 Proposition 1.6 の模型比較の余極限保存の補助。
使われ方：自由な退化の関手の余連続性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits Opposite

/--
概要：固定した単体次数からの全射の形。
方針：終域と全射とその全射性だけを保持する。
規約：この添字の型は小さい宇宙にある。
使われ方：次数ごとの評価関手の直和の添字。
-/
structure FreeDegeneracyShape (d : SimplexCategoryᵒᵖ) where
  degree : SimplexCategory
  epi : d.unop ⟶ degree
  epi_property : Epi epi

/--
概要：自由な退化の標準形は、全射の形と対応する元の単体の組である。
方針：標準形の三つの形のフィールドを組にまとめる。
規約：全射性の証明の値には依存しない。
使われ方：型の直和による次数ごとの表示。
-/
def freeDegeneracyShapeEquiv (X : SSet.{u}) (d : SimplexCategoryᵒᵖ) :
    FatNormalForm (discreteRowsFunctor.obj X) d ≃
      (Σ s : FreeDegeneracyShape d, X.obj (op s.degree)) where
  toFun p := ⟨⟨p.degree, p.epi, p.epi_property⟩, p.simplex⟩
  invFun p := ⟨p.1.degree, p.1.epi, p.1.epi_property, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/--
概要：各全射の形の終域で単体集合を評価する図式の関手。
方針：形の離散圏を添字として評価関手を並べる。
規約：射は元の単体写像の対応する次数の成分。
使われ方：直和と余極限の交換を適用するための実際の図式。
-/
def freeDegeneracyShapeDiagram (d : SimplexCategoryᵒᵖ) :
    SSet.{u} ⥤ Discrete (FreeDegeneracyShape d) ⥤ Type u where
  obj X := Discrete.functor (fun s => X.obj (op s.degree))
  map f := Discrete.natTrans (fun s => f.app (op s.as.degree))

/--
概要：次数ごとの自由な退化と、評価関手の直和の間の同型。
方針：標準形の同値と、型の直和の普遍的な同型を合成する。
規約：自然性は別途計算する。
使われ方：次数ごとの余極限保存の移送。
-/
def freeDegeneracyShapeColimitIso (X : SSet.{u}) (d : SimplexCategoryᵒᵖ) :
    (freeDegeneracies.obj X).obj d ≅ colimit ((freeDegeneracyShapeDiagram d).obj X) :=
  Equiv.toIso ((freeDegeneraciesNormalForm X d).trans (freeDegeneracyShapeEquiv X d)) ≪≫
    (Types.coproductIso (fun s : FreeDegeneracyShape d => X.obj (op s.degree))).symm

end SerrePositivity.KST.Comparison
