module

public import SerrePositivity.InfinityCategories.F1.EssentiallySmallFiniteWitness
public import SerrePositivity.InfinityCategories.F1.TransportWitnessRestrictionFibration

/-!
概要：essentially small な Kan fiber を持つ任意の底上の表現空間と相対延長空間は可縮。
方針：各標準単体と境界で有限次元の定理を使い、既存のセル帰納法と制限の充填性を適用する。
規約：元の底・全空間の小ささも次数 fiber の小ささも要求しない。
使われ方：相対普遍性定理の空間値版と、全パラメーターでの境界固定延長。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

local instance essentiallySmallWitnessPullbackSndLF {E B D : SSet.{u + 1}}
    (p : E ⟶ B) [LeftFibration p] (g : D ⟶ B) :
    LeftFibration (pullback.snd p g) :=
  ⟨leftFibrations.pullback_snd p g (LeftFibration.mem (p := p))⟩

/-- 任意の底上で、各 Kan fiber が小さい模型を持つ実際の表現空間は可縮。 -/
lemma essentiallySmallTransportWitnessSpace_isContractibleKan {E B : SSet.{u + 1}}
    (p : E ⟶ B) [LeftFibration p] (hp : HasEssentiallySmallFibers p) :
    IsContractibleKan (transportWitnessSpace p) := by
  apply transportWitnessSpace_isContractibleKan_of_simplexes_and_boundaries p
  · intro n σ
    change IsContractibleKan (transportWitnessSpace (pullback.fst σ p))
    have : LeftFibration (pullback.fst σ p) :=
      ⟨leftFibrations.pullback_fst σ p (LeftFibration.mem (p := p))⟩
    exact essentiallySmallFiniteTransportWitnessSpace_isContractibleKan (n + 1)
      (pullback.fst σ p) (hp.pullback_fst σ)
  · intro n σ
    change IsContractibleKan (transportWitnessSpace (pullback.fst (∂Δ[n].ι ≫ σ) p))
    have : LeftFibration (pullback.fst (∂Δ[n].ι ≫ σ) p) :=
      ⟨leftFibrations.pullback_fst _ p (LeftFibration.mem (p := p))⟩
    exact essentiallySmallFiniteTransportWitnessSpace_isContractibleKan n
      (pullback.fst (∂Δ[n].ι ≫ σ) p) (hp.pullback_fst (∂Δ[n].ι ≫ σ))

/-- 概要：essentially small fiber の表現空間の単射制限は trivial Kan fibration。
方針：両側の表現空間の可縮性と制限の全ホーン充填を合わせる。
規約：部分底の大きさも制限しない。
使われ方：全パラメーターにわたる境界固定の表現の延長。 -/
lemma essentiallySmallTransportWitnessRestriction_trivialKanFibration {E B D : SSet.{u + 1}}
    (p : E ⟶ B) [LeftFibration p] (hp : HasEssentiallySmallFibers p) (g : D ⟶ B) [Mono g] :
    TrivialKanFibration (transportWitnessRestriction p g) := by
  have := transportWitnessRestriction_fibration p g
  exact trivialKanFibration_of_fibration_of_contractible _
    (essentiallySmallTransportWitnessSpace_isContractibleKan p hp)
    (essentiallySmallTransportWitnessSpace_isContractibleKan (pullback.snd p g) (hp.pullback_snd g))

/-- 概要：境界の表現を固定した延長空間はessentially small fiber の場合も可縮。
方針：単射制限の trivial Kan fibration の fiber を取る。
規約：底と全空間の小ささは不要。
使われ方：任意の底上の境界固定の選択独立性。 -/
lemma essentiallySmallTransportRepresentationExtension_isContractibleKan {E B D : SSet.{u + 1}}
    (p : E ⟶ B) [LeftFibration p] (hp : HasEssentiallySmallFibers p) (g : D ⟶ B) [Mono g]
    (R : LeftTransportRepresentation (pullback.snd p g)) :
    IsContractibleKan
      (vertexFiber (transportWitnessRestriction p g) (transportWitnessVertex R)) := by
  have := essentiallySmallTransportWitnessRestriction_trivialKanFibration p hp g
  exact vertexFiber_isContractibleKan _ _

/-- 概要：essentially small fiber の left fibration は実際の表現を持つ。
方針：可縮な表現空間の頂点を表現へ戻す。
規約：表現の存在を追加仮定に置かない。
使われ方：任意の底上の絶対的な分類図式の存在。 -/
lemma essentiallySmallLeftTransportRepresentation_nonempty {E B : SSet.{u + 1}}
    (p : E ⟶ B) [LeftFibration p] (hp : HasEssentiallySmallFibers p) :
    Nonempty (LeftTransportRepresentation p) := by
  obtain ⟨v⟩ := (essentiallySmallTransportWitnessSpace_isContractibleKan p hp).nonempty
  exact ⟨(transportWitnessVertexEquiv p).symm v⟩

/-- 概要：任意の単射の上の表現をessentially small fiber の元の射影へ厳密に延長する。
方針：表現空間の制限の厳密な切断を実際の表現へ戻す。
規約：分類図式と全空間の射を同時に固定する。
使われ方：任意の底上の相対的な表現の存在。 -/
lemma exists_essentiallySmall_leftTransportRepresentation_extension {E B D : SSet.{u + 1}}
    (p : E ⟶ B) [LeftFibration p] (hp : HasEssentiallySmallFibers p) (g : D ⟶ B) [Mono g]
    (R : LeftTransportRepresentation (pullback.snd p g)) :
    ∃ S : LeftTransportRepresentation p, S.restrict g = R := by
  have := essentiallySmallTransportWitnessRestriction_trivialKanFibration p hp g
  obtain ⟨s, hs⟩ := trivialKanFibration_exists_section (transportWitnessRestriction p g)
  obtain ⟨S, hS⟩ := transportWitnessVertex_surjective p (s.app _ (transportWitnessVertex R))
  refine ⟨S, transportWitnessVertex_injective _ ?_⟩
  rw [← transportWitnessRestriction_vertex, hS]
  exact congrArg (fun k ↦ k.app (Opposite.op ⦋0⦌) (transportWitnessVertex R)) hs

/-- 概要：部分パラメーター上の指定延長を保って表現の族を同時に延長する。
方針：境界制限の trivial Kan fibration の単射に対する持ち上げ性を使う。
規約：パラメーターも底も小ささを要求しない。
使われ方：任意の底上の高次の境界固定延長。 -/
lemma exists_essentiallySmall_transportWitnessFamily_lift {E B D K L : SSet.{u + 1}}
    (p : E ⟶ B) [LeftFibration p] (hp : HasEssentiallySmallFibers p) (g : D ⟶ B) [Mono g]
    (j : K ⟶ L) [Mono j] (a : K ⟶ transportWitnessSpace p)
    (b : L ⟶ transportWitnessSpace (pullback.snd p g))
    (sq : CommSq a j (transportWitnessRestriction p g) b) :
    ∃ F : L ⟶ transportWitnessSpace p, j ≫ F = a ∧ F ≫ transportWitnessRestriction p g = b := by
  have := essentiallySmallTransportWitnessRestriction_trivialKanFibration p hp g
  have := (TrivialKanFibration.mem (p := transportWitnessRestriction p g)) j inferInstance
  exact ⟨sq.lift, sq.fac_left, sq.fac_right⟩

end SerrePositivity.InfinityCategories
