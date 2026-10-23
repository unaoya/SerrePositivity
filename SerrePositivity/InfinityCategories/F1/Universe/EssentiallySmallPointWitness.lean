module

public import SerrePositivity.InfinityCategories.F1.Universe.SmallKanModel
public import SerrePositivity.InfinityCategories.F1.Transport.RepresentationPrecompose

/-!
概要：小さい Kan 模型を持つ大きい全空間の点上の表現空間は可縮 Kan。
方針：小さい模型の表現を同値の逆で前合成し、元の全空間の実際の表現を作る。
規約：各次数の小ささは要求しない。表現の存在は小さい模型から証明する。
使われ方：essentially small fiber の相対延長の点上の初期段階。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 小さい Kan 模型から、元の大きい点上の射影の実際の表現を構成する。 -/
lemma pointWitnessSpace_nonempty_of_smallKanModel (E : SSet.{u + 1}) [KanComplex E]
    (hE : HasSmallKanModel E) :
    Nonempty ((transportWitnessSpace (transportPointProjection E)) _⦋0⦌) := by
  obtain ⟨K, ⟨e⟩⟩ := hE
  let q := transportPointProjection ((SSet.uliftFunctor.{u + 1, u}).obj K.obj)
  let p := transportPointProjection E
  let R : LeftTransportRepresentation q :=
    (transportWitnessVertexEquiv q).symm (Classical.choice (smallPointWitnessSpace_nonempty K.obj))
  have hf : e.inv ≫ q = p := stdSimplex.isTerminalObj₀.hom_ext _ _
  let S := R.precompose e.inv hf (fun b ↦
    vertexFiberMap_isQCatEquivalence_of_precompositionEquivalence p q e.inv hf
      e.symm.isQCatEquivalence.isPrecompositionEquivalence b)
  exact ⟨transportWitnessVertex S⟩

/-- 小さい Kan 模型を持つ全空間の点上の表現空間は、追加の存在仮定なしに可縮。 -/
lemma pointWitnessSpace_isContractibleKan_of_smallKanModel
    (E : SSet.{u + 1}) [KanComplex E] (hE : HasSmallKanModel E) :
    IsContractibleKan (transportWitnessSpace (transportPointProjection E)) :=
  pointWitnessSpace_isContractibleKan_of_nonempty E
    (pointWitnessSpace_nonempty_of_smallKanModel E hE)

/-- 標準点上の唯一の頂点の fiber の包含は、元の全空間との厳密な同型。 -/
def transportPointFiberIso {E : SSet.{u + 1}}
    (p : E ⟶ (Δ[0] : SSet.{u + 1})) :
    vertexFiber p (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) ≅ E := by
  have : IsIso (vertexFiberι p (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) := by
    rw [NatTrans.isIso_iff_isIso_app]
    rintro ⟨⟨n⟩⟩
    rw [isIso_iff_bijective]
    refine ⟨Subtype.val_injective, ?_⟩
    intro x
    exact ⟨⟨x, stdSimplex_zero_eq_constant (p.app _ x)⟩, rfl⟩
  exact asIso (vertexFiberι p (stdSimplex.obj₀Equiv.symm (0 : Fin 1)))

attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- essentially small fiber の点上の任意の left fibration の表現空間は可縮 Kan。 -/
lemma essentiallySmallPointTransportWitnessSpace_isContractibleKan {E : SSet.{u + 1}}
    (p : E ⟶ (Δ[0] : SSet.{u + 1})) [LeftFibration p]
    (hp : HasEssentiallySmallFibers p) : IsContractibleKan (transportWitnessSpace p) := by
  have : KanComplex E := transportPoint_total_kanComplex p
  have hE : HasSmallKanModel E := (hp _).of_equivalence
    (qCatEquivalenceOfIso (transportPointFiberIso p))
  have he : p = transportPointProjection E := stdSimplex.isTerminalObj₀.hom_ext _ _
  subst p
  exact pointWitnessSpace_isContractibleKan_of_smallKanModel E hE

end SerrePositivity.InfinityCategories
