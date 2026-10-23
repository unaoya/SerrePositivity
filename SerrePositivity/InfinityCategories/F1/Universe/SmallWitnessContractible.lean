module

public import SerrePositivity.InfinityCategories.F1.Universe.SmallFiniteWitnessContractible

/-!
概要：次数ごとに小さい全空間を持つ任意の底上の表現空間は可縮 Kan。
方針：標準単体と境界への底変換に有限次元の定理を適用しセル帰納法へ渡す。
規約：底の有限次元性や次数ごとの小ささは仮定しない。
使われ方：一般の境界固定延長と表現の選択独立性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：各次数で小さい全空間を持つ任意の left fibration の表現空間は可縮 Kan。
方針：有限次元の標準単体・境界での可縮性を実際のセル帰納法で大域へ貼る。
規約：表現の存在も底の小ささも追加仮定にしない。
使われ方：Kerodon Theorem 5.6.8.3 の全空間が次数ごとに小さい場合。 -/
lemma smallTransportWitnessSpace_isContractibleKan {E B : SSet.{u + 1}}
    [∀ m, Small.{u} (E.obj m)] (p : E ⟶ B) [LeftFibration p] :
    IsContractibleKan (transportWitnessSpace p) := by
  apply transportWitnessSpace_isContractibleKan_of_simplexes_and_boundaries p
  · intro n σ
    change IsContractibleKan (transportWitnessSpace (pullback.fst σ p))
    have : LeftFibration (pullback.fst σ p) :=
      ⟨leftFibrations.pullback_fst σ p (LeftFibration.mem (p := p))⟩
    have : ∀ m, Small.{u} ((pullback σ p).obj m) :=
      fun m ↦ transportPullback_obj_small σ p m
    exact smallFiniteTransportWitnessSpace_isContractibleKan (n + 1) (pullback.fst σ p)
  · intro n σ
    change IsContractibleKan (transportWitnessSpace (pullback.fst (∂Δ[n].ι ≫ σ) p))
    have : LeftFibration (pullback.fst (∂Δ[n].ι ≫ σ) p) :=
      ⟨leftFibrations.pullback_fst _ p (LeftFibration.mem (p := p))⟩
    have : ∀ m, Small.{u} ((pullback (∂Δ[n].ι ≫ σ) p).obj m) :=
      fun m ↦ transportPullback_obj_small _ p m
    exact smallFiniteTransportWitnessSpace_isContractibleKan n (pullback.fst (∂Δ[n].ι ≫ σ) p)

/-- 概要：各次数で小さい全空間を持つ left fibration は実際の表現を持つ。
方針：可縮な表現空間の頂点を実際の表現へ戻す。
規約：分類図式と全空間の写像を同時に構成する。
使われ方：相対境界延長を指定する前の絶対的な存在。 -/
lemma smallLeftTransportRepresentation_nonempty {E B : SSet.{u + 1}}
    [∀ m, Small.{u} (E.obj m)] (p : E ⟶ B) [LeftFibration p] :
    Nonempty (LeftTransportRepresentation p) := by
  obtain ⟨v⟩ := (smallTransportWitnessSpace_isContractibleKan p).nonempty
  exact ⟨(transportWitnessVertexEquiv p).symm v⟩

end SerrePositivity.InfinityCategories
