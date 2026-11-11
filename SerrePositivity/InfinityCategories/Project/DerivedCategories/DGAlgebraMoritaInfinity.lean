module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraExtensionInfinity
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleMoritaInfinity
/-!
概要：非可換 dg 代数の Morita 同値と準同型は、実相対 tensor による導来 ∞ 圏同値を与える。
方針：主導来延長の同値性を全 Hom 検査へ移し、一対象の本質的全射性を使う。
規約：基礎環上の平坦性を仮定しない。使われ方：β5 の D(A) の Morita 不変性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory HomologicalComplex DifferentialGraded SSet
variable (R : Type u) [CommRing R] {B C : Mon (Complex R)}
/-- Morita 射の実相対 tensor は、非可換 dg 代数の導来 ∞ 圏同値。 -/
theorem dgAlgebraExtensionInfinity_isQCatEquivalence_of_morita (f : B ⟶ C)
    [(dgDerivedExtension R _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R f)).IsEquivalence] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraExtensionInfinity R f) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleExtensionInfinity_isQCatEquivalence_of_morita R _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R f)
/-- 非可換 dg 代数の準同型は、一対象 dg 圏の実準同値。 -/
lemma dgAlgebraMap_quasiEquivalence (f : B ⟶ C) (hf : QuasiIso f.hom) :
    QuasiEquivalence (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R f) := by
  refine ⟨fun _ _ => hf, ?_⟩
  let ub : Unique (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R B) := {
    default := Opposite.op .star
    uniq x := congrArg Opposite.op (Subsingleton.elim x.unop .star) }
  let uc : Unique (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R C) := {
    default := Opposite.op .star
    uniq x := congrArg Opposite.op (Subsingleton.elim x.unop .star) }
  let : Unique (ClosedCategory R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R B)) := ub
  let : Unique (ClosedCategory R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R C)) := uc
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R f).onHomotopy.essSurj_of_surj
    (fun y => ⟨default, Subsingleton.elim _ y⟩)
/-- 準同型な非可換 dg 代数は、実相対 tensor による導来 ∞ 圏同値を持つ。 -/
theorem dgAlgebraExtensionInfinity_isQCatEquivalence_of_quasiIso (f : B ⟶ C)
    (hf : QuasiIso f.hom) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraExtensionInfinity R f) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleExtensionInfinity_isQCatEquivalence_of_quasiEquivalence R _ _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R f) (dgAlgebraMap_quasiEquivalence R f hf)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
