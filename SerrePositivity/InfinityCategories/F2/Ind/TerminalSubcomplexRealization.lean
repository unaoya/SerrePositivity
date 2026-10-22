module

public import SerrePositivity.InfinityCategories.F2.Ind.TerminalCarrierRealization

/-!
概要：小さい終頂点付き部分複体の包含順の nerve から元の単体集合への実際の写像。
方針：各部分複体の終頂点を選び、全鎖を実現する同じ切断を使う。
規約：写像と部分複体への所属を先に構成する。cofinal 性はこの存在から主張しない。
使われ方：κ-filtered な通常の poset による添字の置き換え。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable (κ : Cardinal.{u}) (X : SSet.{u})

/-- 元の部分複体の中にある、同じ指定終頂点。 -/
def terminalSubcomplexChosenVertex
    (A : SmallSubcomplexFamily κ X (terminalSubcomplexPredicate X)) : A.val.toSSet _⦋0⦌ :=
  Classical.choose A.property.2

/-- 選んだ同じ頂点の元の部分複体内での終対象性。 -/
lemma terminalSubcomplexChosenVertex_terminal
    (A : SmallSubcomplexFamily κ X (terminalSubcomplexPredicate X)) :
    IsTerminalVertex (terminalSubcomplexChosenVertex κ X A) := Classical.choose_spec A.property.2

/-- 同じ小さい終頂点付き部分複体の包含順の全鎖を、元の単体集合内に実現する。 -/
def terminalSubcomplexRealization :
    nerve (SmallSubcomplexFamily κ X (terminalSubcomplexPredicate X)) ⟶ X :=
  terminalCarrierRealization (fun A => A.val) (fun _ _ h => h)
    (terminalSubcomplexChosenVertex κ X) (terminalSubcomplexChosenVertex_terminal κ X)

/-- 同じ実現の各零単体の値は、その添字で選んだ元の終頂点。 -/
lemma terminalSubcomplexRealization_vertex
    (g : (Δ[0] : SSet.{u}) ⟶ nerve (SmallSubcomplexFamily κ X (terminalSubcomplexPredicate X))) :
    g ≫ terminalSubcomplexRealization κ X =
      SSet.yonedaEquiv.symm
        (terminalSubcomplexChosenVertex κ X ((SSet.yonedaEquiv g).obj 0)).val :=
  terminalCarrierRealization_vertex _ _ _ _ g

/-- 同じ有限鎖の実現は、最後の元の部分複体の中に含まれる。 -/
lemma terminalSubcomplexRealization_range_le {n : ℕ}
    (q : (Δ[n] : SSet.{u}) ⟶ nerve (SmallSubcomplexFamily κ X (terminalSubcomplexPredicate X))) :
    Subcomplex.range (q ≫ terminalSubcomplexRealization κ X) ≤
      ((SSet.yonedaEquiv q).obj (Fin.last n)).val :=
  terminalCarrierRealization_range_le _ _ _ _ q

/-- ラベル付き積の同じ包含順から元の底への実際の写像。 -/
def terminalSubcomplexBaseMap (C : SSet.{u}) (T : Type u) :
    nerve (SmallSubcomplexFamily κ (C ⊗ nerve (Codiscrete T))
      (terminalSubcomplexPredicate _)) ⟶ C :=
  terminalSubcomplexRealization κ _ ≫ fst _ _

end SerrePositivity.InfinityCategories.F2.Ind
