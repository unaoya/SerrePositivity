module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleResolvedChangeComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelTensorDegreeSurjective
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelComparisonNaturality
/-!
概要：双加群の次数別全射準同型は、元の実導来作用の全関手同型を与える。
方針：同じ半自由入力上の全 Hom 自然性・準同型性・全射性を実分解変更へ渡す。
規約：出力の射影性も局所 Hom の平坦性も不要。使われ方：一般双加群の導来比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (D E : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
  {P Q : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E D} (f : P ⟶ Q)
/-- 同じ半自由入力上の実 tensor 比較射は、双加群準同型を準同型へ送る。 -/
lemma dgSemifreeKernelMap_quasiIso (hf : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.quasiIso R E D f)
    (M : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) : moduleQuasiIso R E (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelMap R D E f M) :=
  _root_.SerrePositivity.DifferentialGraded.Morita.kernelTensorMap_projective_quasiIso R D E f hf
    (ForgetEnrichment.of (Complex R) M.val) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeModule_isProjective R D M)
/-- 同じ半自由入力上の実 tensor 比較射は、全評価の全次数全射性を保つ。 -/
lemma dgSemifreeKernelMap_degree_surjective
    (hf : ∀ (e : E) (d : D) (j : ℤ),
      Function.Surjective (((_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.valueEvaluation R E D e d).map f).f j))
    (M : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) :
    moduleDegreewiseSurjective R E (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelMap R D E f M) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTensorMap_degree_surjective R D E f hf (ForgetEnrichment.of (Complex R) M.val)
/-- 双加群の次数別全射準同型に沿う、元の実導来作用の全関手同型。 -/
def dgKernelDerivedInfinity_mapIso_of_surjective_quasiIso
    (hf : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.quasiIso R E D f)
    (hs : ∀ (e : E) (d : D) (j : ℤ),
      Function.Surjective (((_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.valueEvaluation R E D e d).map f).f j)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D E (BimoduleCategory.underlying R E D P))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D E (BimoduleCategory.underlying R E D Q)) := by
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_changeIso R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) E
    (F := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG R D E (BimoduleCategory.underlying R E D P))
    (G := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG R D E (BimoduleCategory.underlying R E D Q))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelMap R D E f)
    (dgSemifreeKernelMap_degree_surjective R D E f hs)
    (dgSemifreeKernelMap_quasiIso R D E f hf)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelMap_hom_naturality R D E f)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
