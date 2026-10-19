module
public import SerrePositivity.InfinityCategories.Derived.DGQuotientExactFunctor
public import SerrePositivity.InfinityCategories.Derived.ResolvedDGQuotientZeroObjects
public import SerrePositivity.InfinityCategories.Stable.StableVertexClosure

/-! # 実 dg 商が反転する cofiber 辺

概要：指定対象の安定閉包に cofiber を持つ全ての実辺を、平坦模型による商関手は反転。
方針：実商の完全性と指定頂点の零化を、一般の cofiber 辺の判定へ渡す。
規約：全 ∞ 関手圏の局所化普遍性は別途必要。使われ方：F1B の局所化の入口。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 指定 dg 対象の実安定閉包と同型な cofiber を持つ辺のクラス。 -/
def dgVerdierEdges (P : Set D) : Set ((dgNerve A D) _⦋1⦌) :=
  cofiberLocalizingEdges {x | StableVertexClosure (Simplex.vertex '' P) x}

omit [Small.{u} D] in
/-- Verdier 辺の所属は、任意の実 cofiber による安定閉包の所属で判定できる。 -/
lemma dgVerdierEdges_mem_iff (P : Set D) {a : (dgNerve A D) _⦋1⦌}
    (s : CofiberSquare (edgeOfSimplex a)) :
    a ∈ dgVerdierEdges A D P ↔ StableVertexClosure (Simplex.vertex '' P) s.cofiber :=
  cofiberStableEdges_mem_iff _ s

/-- 任意の安定標的への完全関手について、指定対象の零化と cofiber 辺の反転は同値。 -/
theorem dgVerdierEdges_inverts_iff_kills [IsDGPretriangulated A D]
    {Y : SSet.{max u v}} [Quasicategory Y] [IsStable Y]
    (F : dgNerve A D ⟶ Y) [IsExactFunctor F] (P : Set D) :
    InvertsEdges F (dgVerdierEdges A D P) ↔
      ∀ b : P, IsZeroVertex (F.app (Opposite.op ⦋0⦌) (Simplex.vertex b.val)) := by
  let := dgNerve_isStable_of_pretriangulated A D
  rw [dgVerdierEdges, inverts_stableVertexClosureEdges_iff_kills]
  constructor
  · intro h b
    exact h _ ⟨b.val, b.property, rfl⟩
  · rintro h _ ⟨b, hb, rfl⟩
    exact h ⟨b, hb⟩

/-- 局所 K-flat な商への実射影は、指定対象の cofiber 辺を全て反転。 -/
theorem dgQuotientNerveProjection_invertsVerdierEdges [IsDGPretriangulated A D]
    (P : Set D) (h : DGQuotient.localKFlat A D P) :
    InvertsEdges (dgQuotientNerveProjection A D P) (dgVerdierEdges A D P) := by
  let := dgQuotientNerve_isStable A D P h
  let := dgQuotientNerveProjection_isExactFunctor A D P h
  exact (dgVerdierEdges_inverts_iff_kills A D _ P).2 (dgQuotientNerveProjection_kills A D P)

/-- 元の Hom の平坦性を仮定せず、平坦分解後の商関手は cofiber 辺を全て反転。 -/
theorem resolvedDGQuotientFunctor_invertsVerdierEdges [IsDGPretriangulated A D]
    (P : Set D) : InvertsEdges (resolvedDGQuotientFunctor A D P) (dgVerdierEdges A D P) := by
  let := resolvedDGQuotientNerve_isStable A D P
  let := resolvedDGQuotientFunctor_isExactFunctor A D P
  exact (dgVerdierEdges_inverts_iff_kills A D _ P).2 (resolvedDGQuotientFunctor_kills A D P)

/-- 任意の標的への実前合成を、cofiber 辺を反転する全関手の部分圏へ因子分解。 -/
def resolvedDGQuotientLocalizationPrecomposition [IsDGPretriangulated A D]
    (P : Set D) (Y : SSet.{max u v}) :
    (ihom (resolvedDGQuotientNerve A D P)).obj Y ⟶
      (invertingFunctors (dgNerve A D) Y (dgVerdierEdges A D P) : SSet.{max u v}) :=
  localizationPrecomposition (resolvedDGQuotientFunctor A D P) (dgVerdierEdges A D P)
    (resolvedDGQuotientFunctor_invertsVerdierEdges A D P) Y

/-- 反転関手の部分圏への因子分解は、元の実前合成と厳密に一致する。 -/
lemma resolvedDGQuotientLocalizationPrecomposition_ι [IsDGPretriangulated A D]
    (P : Set D) (Y : SSet.{max u v}) :
    resolvedDGQuotientLocalizationPrecomposition A D P Y ≫
      (invertingFunctors (dgNerve A D) Y (dgVerdierEdges A D P)).ι =
        (MonoidalClosed.pre (resolvedDGQuotientFunctor A D P)).app Y :=
  localizationPrecomposition_ι _ _ _ _

end SerrePositivity.InfinityCategories
