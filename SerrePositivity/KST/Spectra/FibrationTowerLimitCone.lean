module

public import SerrePositivity.KST.Spectra.FibrationTower
public import Mathlib.CategoryTheory.Functor.OfSequence

/-!
概要：整合族で定義した具体的な塔の極限を通常の極限錐として表す。
方針：隣接射での整合性から自然変換を作り、明示した lift と外延性を使う。
規約：極限の普遍性には Kan 性も fibration 性も不要。
使われ方：Goerss–Jardine VIII §1。写像空間の復元と具体的な塔の π の比較。
-/

@[expose] public section
universe u
open CategoryTheory Limits SSet Opposite

namespace SerrePositivity.KST.Spectra.FibrationTower

variable (D : ℕᵒᵖ ⥤ SSet.{u})

/-- 具体的な整合族の極限を頂点とする錐。 -/
def sequentialCone : Cone D where
  pt := limit (fun n ↦ D.obj (op n)) (fun n ↦ D.map (homOfLE (Nat.le_succ n)).op)
  π := NatTrans.ofOpSequence
    (fun n ↦ projection (fun n ↦ D.obj (op n))
      (fun n ↦ D.map (homOfLE (Nat.le_succ n)).op) n)
    (fun n ↦ by
      change 𝟙 _ ≫ _ = _
      rw [Category.id_comp, projection_comp])

/-- 錐の射影は整合族の座標評価そのもの。 -/
lemma sequentialCone_π (n : ℕ) : (sequentialCone D).π.app (op n) =
    projection (fun n ↦ D.obj (op n)) (fun n ↦ D.map (homOfLE (Nat.le_succ n)).op) n := rfl

/-- 具体的な整合族の錐は通常の極限錐。 -/
def sequentialConeIsLimit : IsLimit (sequentialCone D) where
  lift s := lift _ _ (fun n ↦ s.π.app (op n)) (fun n ↦ s.w _)
  fac s n := by
    exact lift_projection _ _ _ _ n.unop
  uniq s m hm := by
    apply hom_ext (fun n ↦ D.obj (op n)) (fun n ↦ D.map (homOfLE (Nat.le_succ n)).op)
    intro n
    rw [lift_projection]
    exact hm (op n)

end SerrePositivity.KST.Spectra.FibrationTower
