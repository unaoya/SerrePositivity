module
public import SerrePositivity.KST.Fibration.SimplexFiberBaseChange
public import SerrePositivity.KST.SConstruction.SimplicialProductQuillenA

/-! # 単体積版 Quillen A の厳密な引き戻しに沿う基底変換

元の全単体左 fiber で quotient 比較が局所化同型なら、任意の基底変換後も同じ条件が成立する。
元の二成分の射対を結論し、実現の引き戻し保存を仮定しない。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.KST.SConstruction
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration

/-- 元の単体 fiber 条件は、同じ厳密引き戻しの全単体 fiber に基底変換される。 -/
lemma simplexFiberQuotient_baseChange {P X A Y Z : SSet.{u}}
    {p : P ⟶ X} {q : P ⟶ A} {f : X ⟶ Y} {u : A ⟶ Y}
    (h : IsPullback p q f u) (g : X ⟶ Z)
    (hf : ∀ (m : ℕ) (y : Y _⦋m⦌), IsIso (AnodyneHomotopy.anodyneQ.map
      (simplexLeftFiberProjection f y ≫ g))) (m : ℕ) (a : A _⦋m⦌) :
    IsIso (AnodyneHomotopy.anodyneQ.map (simplexLeftFiberProjection q a ≫ (p ≫ g))) := by
  have : IsIso (AnodyneHomotopy.anodyneQ.map (simplexFiberBaseChangeHom h a)) :=
    inferInstanceAs (IsIso (AnodyneHomotopy.anodyneQ.map (simplexFiberBaseChangeIso h a).hom))
  have := hf m (u.app (Opposite.op ⦋m⦌) a)
  rw [← Category.assoc, ← simplexFiberBaseChangeHom_projection h a, Category.assoc,
    Functor.map_comp]
  infer_instance

/-- K-2 の元の単体積版 Quillen A は、任意の厳密基底変換後の同じ射対にも適用できる。 -/
theorem productQuillenA_baseChange {P X A Y Z : SSet.{u}}
    {p : P ⟶ X} {q : P ⟶ A} {f : X ⟶ Y} {u : A ⟶ Y}
    (h : IsPullback p q f u) (g : X ⟶ Z)
    (hf : ∀ (m : ℕ) (y : Y _⦋m⦌), IsIso (AnodyneHomotopy.anodyneQ.map
      (simplexLeftFiberProjection f y ≫ g))) :
    IsIso (AnodyneHomotopy.anodyneQ.map (lift q (p ≫ g))) :=
  simplicialProductQuillenA q (p ≫ g) (simplexFiberQuotient_baseChange h g hf)

end SerrePositivity.KST.Fibration
