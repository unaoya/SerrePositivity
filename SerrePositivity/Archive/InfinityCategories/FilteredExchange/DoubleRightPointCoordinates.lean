module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedSlice

/-!
概要：二つの終点を追加した join を、同じ二重終点固定単体へ移す。
方針：元の標準 join 同型を二回使う。
規約：全添字制限を保持。使われ方：同じ指定射を付け足した実錐の座標。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の二つの終点を持つ join の、同じ標準単体への座標。 -/
def doubleRightPointCoordinates (n : ℕ) :
    join (join (Δ[n] : SSet.{u}) Δ[0]) Δ[0] ⟶ Δ[n + 2] :=
  joinMap (joinStdSimplexIso n 0).hom (𝟙 Δ[0]) ≫ (joinStdSimplexIso (n + 1) 0).hom

/-- 二つの元の終点を固定した標準 join の座標は、全添字制限に自然。 -/
lemma doubleRightPointCoordinates_naturality {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌) :
    joinMap (joinMap (stdSimplex.map α) (𝟙 (Δ[0] : SSet.{u}))) (𝟙 Δ[0]) ≫
        doubleRightPointCoordinates n =
      doubleRightPointCoordinates m ≫
        stdSimplex.map (PinchedHom.extend (PinchedHom.extend α)) := by
  unfold doubleRightPointCoordinates
  rw [← Category.assoc, ← joinMap_comp, joinStdSimplexIso_rightPoint_naturality]
  rw [joinMap_comp, Category.assoc, joinStdSimplexIso_rightPoint_naturality]
  simp only [Category.assoc]

end SerrePositivity.InfinityCategories.F2
