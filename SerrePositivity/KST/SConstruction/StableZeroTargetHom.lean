module
public import SerrePositivity.KST.SConstruction.PerfectStableArrow
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.ExactMapHomotopy
public import SerrePositivity.KST.LocalizingInvariants.ZeroMaps
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.PointFunctorEvaluation

/-!
概要：零安定圏を終点とする射の類と、零点図式への全比較の一意性。
方針：元 coherent 辺を完全関手へ戻し、零値関手の全同型を使う。
規約：元頂点・元射の類を保持。使われ方：実右面の既存指定零角比較の回収。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet InfinityCategories LocalizingInvariants
open scoped Simplicial

private lemma stableHomRepresentative (A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u})
    (f : HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableVertex A) ⟶ HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableVertex B)) :
    ∃ F : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B, Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow F).toTruncated = f := by
  obtain ⟨e, he⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective _ _ f
  let a := SSet.Edge.ofTruncated e
  let F := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrowEquiv A B a
  have ha : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow F = a := (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrowEquiv A B).symm_apply_apply a
  have hc : (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow F).toTruncated = e := congrArg SSet.Edge.toTruncated ha
  exact ⟨F, (congrArg Truncated.HomotopyCategory.homMk hc).trans he⟩

/-- 概要：同じ零安定圏へ向かう二射の類は等しい。
方針：元二辺を完全関手へ戻し、同じ零値図式比較を使う。
規約：元射の類を保持。使われ方：零頂点への全比較の一意性。 -/
lemma stableZeroTarget_hom_ext (A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) (hz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory B)
    (f g : HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableVertex A) ⟶ HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableVertex B)) : f = g := by
  obtain ⟨F, hF⟩ := stableHomRepresentative A B f
  obtain ⟨G, hG⟩ := stableHomRepresentative A B g
  exact hF.symm.trans ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.stableArrow_homMk_eq_of_functorIso
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroDiagramFunctorIso _ _ (fun x => hz _) (fun x => hz _))).trans hG)

/-- 概要：任意の同じ零終頂点へ向かう二射の類は等しい。
方針：元頂点と束ねた安定圏の頂点等号で前補題を輸送する。
規約：元頂点を変更しない。使われ方：元図式の零角射の類。 -/
lemma stableZeroVertexTarget_hom_ext (x y : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} _⦋0⦌)
    (hz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject y)) (f g : HomotopyCategory.mk x ⟶ HomotopyCategory.mk y) :
    f = g := by
  have hx := congrArg HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableVertex_object x)
  have hy := congrArg HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableVertex_object y)
  have h := stableZeroTarget_hom_ext (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject x) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject y) hz
    (eqToHom hx ≫ f ≫ eqToHom hy.symm) (eqToHom hx ≫ g ≫ eqToHom hy.symm)
  apply (cancel_epi (eqToHom hx)).1
  apply (cancel_mono (eqToHom hy.symm)).1
  exact (Category.assoc _ _ _).trans (h.trans (Category.assoc _ _ _).symm)

/-- 概要：Cat^perf の同じ零終頂点へ向かう二射の類は等しい。
方針：元包含の充満忠実性で元安定圏値の等号を反映する。
規約：元完備頂点を保持。使われ方：指定零角同型の一意性。 -/
lemma perfectZeroVertexTarget_hom_ext (x y : perfectStableInfinity.{u} _⦋0⦌)
    (hz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory (perfectStableObject y))
    (f g : HomotopyCategory.mk x ⟶ HomotopyCategory.mk y) : f = g := by
  apply perfectStableInfinityInclusion_isFullyFaithful.toHoFullyFaithful.map_injective
  exact stableZeroVertexTarget_hom_ext _ _ hz _ _

/-- 概要：同じ零点 Cat^perf 図式への二全比較は等しい。
方針：零単体の関手評価の充満忠実性と零終頂点の射の類の一意性を使う。
規約：元の二指定比較を保持。使われ方：実右面の既存零角比較との一致。 -/
lemma perfectZeroPointFunctorIso_ext (f g : (Δ[0] : SSet.{u + 1}) ⟶ perfectStableInfinity.{u})
    (hz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory (perfectStableObject (g.app _ (stdSimplex.obj₀Equiv.symm 0))))
    (e e' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) : e = e' := by
  let p := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.pointFunctorEvaluationIso perfectStableInfinity.{u}).hom
  have hp := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.pointFunctorEvaluationIso
    perfectStableInfinity.{u})).isQCatEquivalence.isFullyFaithful
  apply Iso.ext
  apply hp.toHoFullyFaithful.map_injective
  apply perfectZeroVertexTarget_hom_ext
  change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory (perfectStableObject
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := perfectStableInfinity.{u}) (stdSimplex.obj₀Equiv.symm 0)).app _
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex g)))
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex]
  exact hz
end SerrePositivity.KST.SConstruction
