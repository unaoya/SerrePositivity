module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpacePrisms
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.JoinCylinderSimplex

/-!
概要：右 join prism の実単体は、外側時間が零である先頭部分の係数だけに依存する。
方針：同じ切断での join の左右成分を計算する。
規約：元の prism の厳密等式を扱う。使われ方：合成四角形の全図式の折り畳み。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 同じ外側時間の先頭制限が一致すれば、元の右 join prism の値も厳密に一致する。 -/
lemma rightMappingSpacePrism_eq_of_prefix {A : SSet.{u}} {n : ℕ}
    (s : (Δ[1] : SSet.{u}) _⦋n⦌) (a a' : A _⦋n⦌)
    (h : Join.augMap A (Join.prefixIncl (n + 1)
        ((joinStdSimplexIso.{u} 0 0).inv.app (Opposite.op ⦋n⦌) s).1.val
        (Nat.le_of_lt_succ
          ((joinStdSimplexIso.{u} 0 0).inv.app (Opposite.op ⦋n⦌) s).1.isLt)) a =
      Join.augMap A (Join.prefixIncl (n + 1)
        ((joinStdSimplexIso.{u} 0 0).inv.app (Opposite.op ⦋n⦌) s).1.val
        (Nat.le_of_lt_succ
          ((joinStdSimplexIso.{u} 0 0).inv.app (Opposite.op ⦋n⦌) s).1.isLt)) a') :
    (rightMappingSpacePrism A).app (Opposite.op ⦋n⦌) (s, a) =
      (rightMappingSpacePrism A).app (Opposite.op ⦋n⦌) (s, a') := by
  change (joinCylinderMap A Δ[0]).app (Opposite.op ⦋n⦌)
      ((a, s), PinchedHom.constant (stdSimplex.obj₀Equiv.symm 0) n) =
    (joinCylinderMap A Δ[0]).app (Opposite.op ⦋n⦌)
      ((a', s), PinchedHom.constant (stdSimplex.obj₀Equiv.symm 0) n)
  rw [joinCylinderMap_app, joinCylinderMap_app]
  exact Join.Simplex.ext (K := A) (L := Δ[0]) _ _ rfl h rfl

end SerrePositivity.InfinityCategories.F2
