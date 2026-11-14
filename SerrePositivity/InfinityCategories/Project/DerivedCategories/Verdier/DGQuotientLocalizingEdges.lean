module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGQuotientExactFunctor
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.ResolvedDGQuotientZeroObjects
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure

/-! # 実 dg 商が反転する cofiber 辺

概要：指定対象の安定閉包に cofiber を持つ全ての実辺を、平坦模型による商関手は反転。
方針：実商の完全性と指定頂点の零化を、一般の cofiber 辺の判定へ渡す。
規約：全 ∞ 関手圏の局所化普遍性は別途必要。使われ方：F1B の局所化の入口。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]

/-- 指定 dg 対象の実安定閉包と同型な cofiber を持つ辺のクラス。 -/
def dgVerdierEdges (P : Set D) : Set ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) _⦋1⦌) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges {x | _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex '' P) x}

omit [Small.{u} D] in
/-- Verdier 辺の所属は、任意の実 cofiber による安定閉包の所属で判定できる。 -/
lemma dgVerdierEdges_mem_iff (P : Set D) {a : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) _⦋1⦌}
    (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.CofiberSquare (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex a)) :
    a ∈ dgVerdierEdges A D P ↔ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex '' P) s.cofiber :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberStableEdges_mem_iff _ s

/-- 任意の安定標的への完全関手について、指定対象の零化と cofiber 辺の反転は同値。 -/
theorem dgVerdierEdges_inverts_iff_kills [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]
    {Y : SSet.{max u v}} [Quasicategory Y] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable Y]
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D ⟶ Y) [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor F] (P : Set D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges F (dgVerdierEdges A D P) ↔
      ∀ b : P, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (F.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex b.val)) := by
  let := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Pretriangulated.dgNerve_isStable_of_pretriangulated A D
  rw [dgVerdierEdges, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.inverts_stableVertexClosureEdges_iff_kills]
  constructor
  · intro h b
    exact h _ ⟨b.val, b.property, rfl⟩
  · rintro h _ ⟨b, hb, rfl⟩
    exact h ⟨b, hb⟩

/-- 局所 K-flat な商への実射影は、指定対象の cofiber 辺を全て反転。 -/
theorem dgQuotientNerveProjection_invertsVerdierEdges [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]
    (P : Set D) (h : _root_.SerrePositivity.DifferentialGraded.DGQuotient.localKFlat A D P) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection A D P) (dgVerdierEdges A D P) := by
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerve_isStable A D P h
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection_isExactFunctor A D P h
  exact (dgVerdierEdges_inverts_iff_kills A D _ P).2 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection_kills A D P)

/-- 元の Hom の平坦性を仮定せず、平坦分解後の商関手は cofiber 辺を全て反転。 -/
theorem resolvedDGQuotientFunctor_invertsVerdierEdges [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]
    (P : Set D) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientFunctor A D P) (dgVerdierEdges A D P) := by
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientNerve_isStable A D P
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientFunctor_isExactFunctor A D P
  exact (dgVerdierEdges_inverts_iff_kills A D _ P).2 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientFunctor_kills A D P)

/-- 任意の標的への実前合成を、cofiber 辺を反転する全関手の部分圏へ因子分解。 -/
def resolvedDGQuotientLocalizationPrecomposition [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]
    (P : Set D) (Y : SSet.{max u v}) :
    (ihom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientNerve A D P)).obj Y ⟶
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertingFunctors (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) Y (dgVerdierEdges A D P) : SSet.{max u v}) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.localizationPrecomposition (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientFunctor A D P) (dgVerdierEdges A D P)
    (resolvedDGQuotientFunctor_invertsVerdierEdges A D P) Y

/-- 反転関手の部分圏への因子分解は、元の実前合成と厳密に一致する。 -/
lemma resolvedDGQuotientLocalizationPrecomposition_ι [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]
    (P : Set D) (Y : SSet.{max u v}) :
    resolvedDGQuotientLocalizationPrecomposition A D P Y ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertingFunctors (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) Y (dgVerdierEdges A D P)).ι =
        (MonoidalClosed.pre (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientFunctor A D P)).app Y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.localizationPrecomposition_ι _ _ _ _

end SerrePositivity.InfinityCategories.Project.DerivedCategories
