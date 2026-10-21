module
public import SerrePositivity.InfinityCategories.Derived.DGHomotopyAdjunctionCounit
public import SerrePositivity.InfinityCategories.Derived.DGClosedPostcompositionEquivalence
/-!
概要：全 Hom 準同型性を持つ実余単位を、元の pinched Hom 空間の普遍性へ送る。
方針：同じ実鎖写像を Dold–Kan の比較へ送り、dg 関手と実後合成との一致を回収する。
規約：対象の小ささは不要。使われ方：一般 RHom の実右随伴の coherent な構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (C E : Type v)
  [DGCategory R C] [DGCategory R E]
/-- 元の dg 関手に対する実閉余単位と、その全 Hom の準同型性。 -/
structure DGUniversalCounit (G : DGFunctor R C E) (y : E) where
  source : C
  counit : ForgetEnrichment.of (Complex R) (G.obj source) ⟶
    ForgetEnrichment.of (Complex R) y
  quasiIso : ∀ x : C, QuasiIso (dgCounitColumn R C E G (t := source) (y := y)
    (closedHomEquiv R E (ForgetEnrichment.of (Complex R) (G.obj source))
      (ForgetEnrichment.of (Complex R) y) counit) x)
namespace DGUniversalCounit
variable {R C E} {G : DGFunctor R C E} {y : E} (e : DGUniversalCounit R C E G y)
/-- 元の dg 関手と同じ実余単位による pinched Hom 空間の写像。 -/
def pinchedMap (x : C) : DGNerve.pinchedHom R C x e.source ⟶
    DGNerve.pinchedHom R E (G.obj x) y :=
  pinchedHomChainMap (dgCounitColumn R C E G (t := e.source) (y := y)
    (closedHomEquiv R E (ForgetEnrichment.of (Complex R) (G.obj e.source))
      (ForgetEnrichment.of (Complex R) y) e.counit) x)
/-- 同じ pinched 写像は、元の dg 関手の像と実余単位による後合成。 -/
lemma pinchedMap_eq (x : C) : e.pinchedMap x =
    pinchedHomChainMap (G.map x e.source) ≫
      pinchedClosedPostcomposition R E (x := G.obj x) e.counit := by
  unfold pinchedMap pinchedClosedPostcomposition
  rw [← pinchedHomChainMap_comp]
  congr 1
  unfold dgCounitColumn
  erw [dgCyclePostcomposition_eq_closed]
/-- 同じ実余単位の写像は、全 pinched Hom 空間のホモトピー同値。 -/
lemma pinchedMap_isSimplicialHomotopyEquivalence (x : C) :
    IsSimplicialHomotopyEquivalence (e.pinchedMap x) := by
  have := e.quasiIso x
  exact pinchedHomChainMap_quasiIso_equivalence
    (dgCounitColumn R C E G (t := e.source) (y := y)
      (closedHomEquiv R E (ForgetEnrichment.of (Complex R) (G.obj e.source))
        (ForgetEnrichment.of (Complex R) y) e.counit) x)
end DGUniversalCounit
end SerrePositivity.InfinityCategories
