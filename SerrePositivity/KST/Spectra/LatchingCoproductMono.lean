module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.Objects
public import Mathlib.CategoryTheory.Types.Monomorphisms
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.Order.SuccPred.Nat

/-!
概要：Type 値の Reedy latching の単射性は実際の余積で閉じる。
方針：latching と評価の余極限保存を使い、各成分の単射の余積として比較射を扱う。
規約：Reedy モデル構造を仮定せず、指定した cofan の普遍性だけを使う。
使われ方：Goerss–Jardine VII §4。BK 重みの各次数の representable 分解への適用。
-/

@[expose] public section
universe u v
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Reedy

namespace SerrePositivity.KST.Spectra.LatchingCoproductMono
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {J : Type v} [SmallCategory J] {inverse direct : MorphismProperty J}
  [inverse.IsMultiplicative] [direct.IsMultiplicative]
  (r : ReedyStructure inverse direct ℕ)
  [∀ j, HasColimitsOfShape (LatchingIndex r j) (Type u)]

/-- 余積の各成分で latching 射が単射なら余積の図式でも単射。 -/
lemma of_cofan {S : Type u} (F : S → J ⥤ Type u) (c : Cofan F) (hc : IsColimit c)
    (j : J) (hF : ∀ s, Mono ((latchingComparison r j).app (F s))) :
    Mono ((latchingComparison r j).app c.pt) := by
  let L : (J ⥤ Type u) ⥤ Type u := latchingEvaluation r j
  let E : (J ⥤ Type u) ⥤ Type u := (evaluation J (Type u)).obj j
  exact MorphismProperty.IsStableUnderColimitsOfShape.condition
    (W := MorphismProperty.monomorphisms (Type u)) (J := Discrete S)
    ((Discrete.functor F) ⋙ L) ((Discrete.functor F) ⋙ E)
    (L.mapCocone c) (E.mapCocone c)
    (isColimitOfPreserves L hc) (isColimitOfPreserves E hc)
    (Functor.whiskerLeft (Discrete.functor F) (latchingComparison r j))
    (fun s ↦ hF s.as) ((latchingComparison r j).app c.pt)
    (fun s ↦ (latchingComparison r j).naturality (c.inj s.as))

end
end SerrePositivity.KST.Spectra.LatchingCoproductMono
