module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.DGHomotopyAdjunctionCounit
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.DGClosedPostcompositionEquivalence
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C E : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E]
/-- 元の dg 関手に対する実閉余単位と、その全 Hom の準同型性。 -/
structure DGUniversalCounit (G : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C E) (y : E) where
  source : C
  counit : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (G.obj source) ⟶
    ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) y
  quasiIso : ∀ x : C, QuasiIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCounitColumn R C E G (t := source) (y := y)
    (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv R E (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (G.obj source))
      (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) y) counit) x)
namespace DGUniversalCounit
variable {R C E} {G : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C E} {y : E} (e : DGUniversalCounit R C E G y)
/-- 元の dg 関手と同じ実余単位による pinched Hom 空間の写像。 -/
def pinchedMap (x : C) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R C x e.source ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R E (G.obj x) y :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCounitColumn R C E G (t := e.source) (y := y)
    (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv R E (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (G.obj e.source))
      (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) y) e.counit) x)
/-- 同じ pinched 写像は、元の dg 関手の像と実余単位による後合成。 -/
lemma pinchedMap_eq (x : C) : e.pinchedMap x =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (G.map x e.source) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPostcomposition R E (x := G.obj x) e.counit := by
  unfold pinchedMap _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPostcomposition
  rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap_comp]
  congr 1
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCounitColumn
  erw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCyclePostcomposition_eq_closed]
/-- 同じ実余単位の写像は、全 pinched Hom 空間のホモトピー同値。 -/
lemma pinchedMap_isSimplicialHomotopyEquivalence (x : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (e.pinchedMap x) := by
  have := e.quasiIso x
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap_quasiIso_equivalence
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCounitColumn R C E G (t := e.source) (y := y)
      (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv R E (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (G.obj e.source))
        (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) y) e.counit) x)
end DGUniversalCounit
end SerrePositivity.InfinityCategories.Project.DerivedCategories
