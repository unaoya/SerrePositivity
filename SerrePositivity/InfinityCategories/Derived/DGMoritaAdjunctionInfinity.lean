module
public import SerrePositivity.InfinityCategories.F1B.QCatEquivalenceAdjunction
public import SerrePositivity.InfinityCategories.Derived.DGAlgebraPerfectMoritaInfinity
public import SerrePositivity.InfinityCategories.F1B.Adjunction.AdjunctionPinchedSpaces
public import SerrePositivity.InfinityCategories.Derived.DGPerfectExtensionCompatibility
/-!
概要：Morita tensor の実 ∞ 同値を、右随伴と全写像空間の随伴比較へ昇格する。
方針：同じ tensor の選択逆を用い、h Fun 内で余単位を adjointify する。
規約：Morita 射の場合。一般 kernel の RHom の構成・同定とは区別する。
使われ方：β5 の Morita tensor の高次随伴と、完全な逆関手。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D E : Type v)
variable [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
variable (F : DGFunctor R D E) [(dgDerivedExtension R D E F).IsEquivalence]
/-- Morita tensor の同じ実逆関手。 -/
def dgMoritaRightAdjointInfinity :
    dgModuleDerivedInfinityCategory R E ⟶ dgModuleDerivedInfinityCategory R D :=
  (dgModuleExtensionInfinity_isQCatEquivalence_of_morita R D E F).choose.inv
/-- Morita tensor と同じ実逆関手の、h Fun 内の三角恒等式を持つ ∞ 随伴。 -/
def dgMoritaAdjunctionInfinity :
    QCatAdjunction (dgModuleExtensionInfinity R D E F)
      (dgMoritaRightAdjointInfinity R D E F) :=
  (dgModuleExtensionInfinity_isQCatEquivalence_of_morita R D E F).choose.toAdjunction
/-- Morita tensor の右随伴は実安定 ∞ 圏間の完全関手。 -/
lemma dgMoritaRightAdjointInfinity_isExactFunctor :
    IsExactFunctor (dgMoritaRightAdjointInfinity R D E F) :=
  isExactFunctor_of_isQCatEquivalence
    (dgModuleExtensionInfinity_isQCatEquivalence_of_morita R D E F).choose.symm.isQCatEquivalence
/-- Morita tensor の随伴による、全 pinched 写像空間の実同値。 -/
def dgMoritaAdjunctionMappingEquivalence
    (x : (dgModuleDerivedInfinityCategory R D) _⦋0⦌)
    (y : (dgModuleDerivedInfinityCategory R E) _⦋0⦌) :
    QCatEquivalence
      (pinchedHom ((dgModuleExtensionInfinity R D E F).app (Opposite.op ⦋0⦌) x) y)
      (pinchedHom x ((dgMoritaRightAdjointInfinity R D E F).app (Opposite.op ⦋0⦌) y)) :=
  (dgMoritaAdjunctionInfinity R D E F).pinchedHomEquivalence x y
/-- Perf 上の Morita tensor の同じ実逆関手。 -/
def dgPerfectMoritaRightAdjointInfinity :
    dgModulePerfectInfinityCategory R E ⟶ dgModulePerfectInfinityCategory R D :=
  (dgPerfectExtensionInfinity_isQCatEquivalence_of_morita R D E F).choose.inv
/-- Perf 上も、同じ実 tensor と選択逆は全関手圏内で随伴する。 -/
def dgPerfectMoritaAdjunctionInfinity :
    QCatAdjunction (dgPerfectExtensionInfinity R D E F)
      (dgPerfectMoritaRightAdjointInfinity R D E F) :=
  (dgPerfectExtensionInfinity_isQCatEquivalence_of_morita R D E F).choose.toAdjunction
/-- Perf 上の Morita tensor の右随伴は完全。 -/
lemma dgPerfectMoritaRightAdjointInfinity_isExactFunctor :
    IsExactFunctor (dgPerfectMoritaRightAdjointInfinity R D E F) :=
  isExactFunctor_of_isQCatEquivalence
    (dgPerfectExtensionInfinity_isQCatEquivalence_of_morita R D E F).choose.symm.isQCatEquivalence
/-- Morita tensor の右随伴も、Perf→D の同じ包含と全関手同型で整合する。 -/
def dgPerfectMoritaRightAdjointInclusionIso :
    FunctorIso (dgPerfectInclusionInfinity R E ≫ dgMoritaRightAdjointInfinity R D E F)
      (dgPerfectMoritaRightAdjointInfinity R D E F ≫ dgPerfectInclusionInfinity R D) :=
  QCatEquivalence.inverseSquareIso
    (dgModuleExtensionInfinity_isQCatEquivalence_of_morita R D E F).choose
    (dgPerfectExtensionInfinity_isQCatEquivalence_of_morita R D E F).choose
    (dgPerfectInclusionInfinity R D) (dgPerfectInclusionInfinity R E)
    (dgPerfectExtensionInclusionIso R D E F)
end SerrePositivity.InfinityCategories
