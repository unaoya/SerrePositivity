module

public import SerrePositivity.InfinityCategories.HomotopyLimits.FiniteProductIndexLegs

/-!
概要：任意の元の非空有限添字族に、元の反復 coherent 積の余極限頂点の積錐を与える。
方針：有限性から標準添字表示を一度選び、元の各因子の図式を厳密に回収する。
規約：元の族を入力とし、選んだ全単射を全宣言で共有する。
使われ方：P_Σ の sifted 閉性で使う一般有限積の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 元の非空有限添字の標準表示を、全単射と共に一度選ぶ。 -/
def nonemptyFiniteIndexPresentation (J : Type u) [Finite J] [Nonempty J] :
    Σ n : ℕ, J ≃ ULift.{u} (Fin (n + 1)) :=
  ⟨Classical.choose (nonemptyFiniteIndex_exists_equiv J),
    Classical.choice (Classical.choose_spec (nonemptyFiniteIndex_exists_equiv J))⟩

/-- 元の非空有限添字族の、同じ標準表示を使う反復 coherent 積図式。 -/
def finiteFamilyCoherentProduct {B : SSet.{u}} {J : Type u} [Finite J] [Nonempty J]
    (G : J → ((SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})) :
    (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u} :=
  let P := nonemptyFiniteIndexPresentation J
  finiteCoherentSpaceProduct P.1 (fun i ↦ G (P.2.symm (ULift.up i)))

/-- 元の任意の非空有限添字族の余極限図式上の native な積錐。 -/
def finiteFamilyProductNativeCone {B : SSet.{u}} [IsSiftedInfinity B]
    {J : Type u} [Finite J] [Nonempty J]
    (G : J → ((SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})) :
    JoinCone (kanDiagramCoherentNerve
      (Discrete.functor (fun j ↦ F2.coherentDiagramTotalKanObject (G j)))) :=
  let P := nonemptyFiniteIndexPresentation J
  (reindexedFiniteProductNativeCone P.1 (fun i ↦ G (P.2.symm (ULift.up i))) P.2).cast
    (reindexedFiniteProductDiagram_original P.1 P.2 G)

/-- 元の族の図式を厳密に保った全錐は、元の余極限頂点を持つ有限積錐。 -/
lemma finiteFamilyProductNativeCone_isLimit {B : SSet.{u}} [IsSiftedInfinity B]
    {J : Type u} [Finite J] [Nonempty J]
    (G : J → ((SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})) :
    IsLimitCone (finiteFamilyProductNativeCone G) := by
  let P := nonemptyFiniteIndexPresentation J
  exact (reindexedFiniteProductNativeCone_isLimit P.1
    (fun i ↦ G (P.2.symm (ULift.up i))) P.2).cast
      (reindexedFiniteProductDiagram_original P.1 P.2 G)

/-- 元の一般有限族の積錐は、同じ反復 coherent 積図式の元の余極限頂点を持つ。 -/
lemma finiteFamilyProductNativeCone_vertex {B : SSet.{u}} [IsSiftedInfinity B]
    {J : Type u} [Finite J] [Nonempty J]
    (G : J → ((SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})) :
    (finiteFamilyProductNativeCone G).vertex =
      coherentNerveVertex (F2.coherentDiagramTotalKanObject (finiteFamilyCoherentProduct G)) := by
  rw [finiteFamilyProductNativeCone, JoinCone.vertex_cast,
    reindexedFiniteProductNativeCone_vertex]
  rfl

/-- 元の一般有限族の全脚も、同じ標準表示の元の脚の全一単体を保持する。 -/
lemma finiteFamilyProductNativeCone_leg_edge {B : SSet.{u}} [IsSiftedInfinity B]
    {J : Type u} [Finite J] [Nonempty J]
    (G : J → ((SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}))
    (j : Discrete J) :
    (F2.nativeConeLeg (finiteFamilyProductNativeCone G)
      (ULift.up (ComposableArrows.mk₀ j))).edge =
        let P := nonemptyFiniteIndexPresentation J
        (F2.nativeConeLeg (finiteSiftedCoherentProductNativeCone P.1
          (fun i ↦ G (P.2.symm (ULift.up i))))
          (ULift.up (ComposableArrows.mk₀ (Discrete.mk (P.2 j.as))))).edge :=
  reindexedFiniteProductNativeCone_leg_edge _ _ _ _

end SerrePositivity.InfinityCategories.HomotopyLimits
