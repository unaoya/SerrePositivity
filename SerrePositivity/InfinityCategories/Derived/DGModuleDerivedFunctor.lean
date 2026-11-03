module
public import SerrePositivity.InfinityCategories.Derived.DGSemifreeProjectiveEquivalence
public import SerrePositivity.InfinityCategories.Derived.DGFullFunctorRestriction
public import SerrePositivity.InfinityCategories.Derived.DGFullInclusionExactReflection
public import SerrePositivity.InfinityCategories.Derived.DGModuleFunctorExact
public import SerrePositivity.DifferentialGraded.Derived.FunctorExtensionAdjunction
/-!
概要：射影的加群を保つ dg 関手と graph 延長を、半自由模型間の実 ∞ 関手にする。
方針：全 Hom を持つ射影的部分圏への実 dg 制限と、証明済み比較同値の逆を使う。
規約：分解を対象ごとに選んだだけの写像で済ませない。使われ方：β5 の相対テンソル。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
variable (R : Type u) [CommRing R] (D E : Type v)
variable [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
/-- 全次数 Hom end を保つ、射影的加群間への dg 制限。 -/
def dgProjectiveModuleFunctor (F : DGFunctor R (RightModule R D) (RightModule R E))
    (hF : ∀ M, dgModuleProjectiveProperty R D M → dgModuleProjectiveProperty R E (F.obj M)) :=
  dgFullFunctorRestriction R (RightModule R D) (RightModule R E) F
    (dgModuleProjectiveProperty R D) (dgModuleProjectiveProperty R E) hF
/-- 射影的加群を保つ dg 関手の実制限は完全。 -/
lemma dgProjectiveModuleFunctorNerve_isExactFunctor
    (F : DGFunctor R (RightModule R D) (RightModule R E))
    (hF : ∀ M, dgModuleProjectiveProperty R D M → dgModuleProjectiveProperty R E (F.obj M)) :
    IsExactFunctor (dgNerve.map (dgProjectiveModuleFunctor R D E F hF)) := by
  let I := dgFullSubcategoryInclusion R (RightModule R D) (dgModuleProjectiveProperty R D)
  let J := dgFullSubcategoryInclusion R (RightModule R E) (dgModuleProjectiveProperty R E)
  let G := dgProjectiveModuleFunctor R D E F hF
  have he : dgNerve.map G ≫ dgNerve.map J = dgNerve.map I ≫ dgNerve.map F := by
    have hd : G.comp J = I.comp F := dgFullFunctorRestriction_inclusion R
      (RightModule R D) (RightModule R E) F _ _ hF
    simpa only [dgNerve.map_comp] using congrArg (fun H => dgNerve.map H) hd
  let := dgProjectiveModuleInclusion_isExactFunctor R D
  let := dgModuleFunctorNerve_isExactFunctor R D E F
  have hc : IsExactFunctor (dgNerve.map G ≫ dgNerve.map J) :=
    he.symm ▸ isExactFunctor_comp (dgNerve.map I) (dgNerve.map F)
  exact isExactFunctor_of_postcomp_dgFullInclusion R (RightModule R E)
    (dgModuleProjectiveProperty R E) (dgNerve.map G)
/-- 射影的加群を保つ実 dg 関手による、半自由模型間の実 ∞ 関手。 -/
def dgModuleDerivedFunctor (F : DGFunctor R (RightModule R D) (RightModule R E))
    (hF : ∀ M, dgModuleProjectiveProperty R D M → dgModuleProjectiveProperty R E (F.obj M)) :
    dgModuleDerivedInfinityCategory R D ⟶ dgModuleDerivedInfinityCategory R E :=
  dgNerve.map (dgSemifreeToProjective R D) ≫ dgNerve.map (dgProjectiveModuleFunctor R D E F hF) ≫
    (dgSemifreeToProjectiveNerve_isQCatEquivalence R E).choose.inv
/-- 構成した ∞ 関手は、射影的模型上の同じ実 dg 関手と一つの全関手同型で比較される。 -/
def dgModuleDerivedFunctor_comparisonIso
    (F : DGFunctor R (RightModule R D) (RightModule R E))
    (hF : ∀ M, dgModuleProjectiveProperty R D M → dgModuleProjectiveProperty R E (F.obj M)) :
    FunctorIso (dgModuleDerivedFunctor R D E F hF ≫ dgNerve.map (dgSemifreeToProjective R E))
      (dgNerve.map (dgSemifreeToProjective R D) ≫
        dgNerve.map (dgProjectiveModuleFunctor R D E F hF)) := by
  have h := (dgSemifreeToProjectiveNerve_isQCatEquivalence R E).choose.invHomIso.precomp
    (dgNerve.map (dgSemifreeToProjective R D) ≫
      dgNerve.map (dgProjectiveModuleFunctor R D E F hF))
  change FunctorIso ((dgNerve.map (dgSemifreeToProjective R D) ≫
    dgNerve.map (dgProjectiveModuleFunctor R D E F hF)) ≫
      ((dgSemifreeToProjectiveNerve_isQCatEquivalence R E).choose.inv ≫
        dgNerve.map (dgSemifreeToProjective R E)))
    ((dgNerve.map (dgSemifreeToProjective R D) ≫
      dgNerve.map (dgProjectiveModuleFunctor R D E F hF)) ≫ 𝟙 _) at h
  simpa only [dgModuleDerivedFunctor, Category.assoc, Category.comp_id] using h
/-- 半自由模型間に作った実 ∞ 関手は完全。 -/
lemma dgModuleDerivedFunctor_isExactFunctor
    (F : DGFunctor R (RightModule R D) (RightModule R E))
    (hF : ∀ M, dgModuleProjectiveProperty R D M → dgModuleProjectiveProperty R E (F.obj M)) :
    IsExactFunctor (dgModuleDerivedFunctor R D E F hF) := by
  let := isExactFunctor_of_isQCatEquivalence (dgSemifreeToProjectiveNerve_isQCatEquivalence R D)
  let := dgProjectiveModuleFunctorNerve_isExactFunctor R D E F hF
  have hi := isExactFunctor_of_isQCatEquivalence
    (dgSemifreeToProjectiveNerve_isQCatEquivalence R E).choose.symm.isQCatEquivalence
  change IsExactFunctor (dgSemifreeToProjectiveNerve_isQCatEquivalence R E).choose.inv at hi
  have : IsExactFunctor (dgNerve.map (dgProjectiveModuleFunctor R D E F hF) ≫
      (dgSemifreeToProjectiveNerve_isQCatEquivalence R E).choose.inv) :=
    isExactFunctor_comp _ _
  exact isExactFunctor_comp _ _
/-- 任意の dg 関手の graph 延長、すなわち相対 tensor の実 ∞ 関手。 -/
def dgModuleExtensionInfinity (F : DGFunctor R D E) :
    dgModuleDerivedInfinityCategory R D ⟶ dgModuleDerivedInfinityCategory R E :=
  dgModuleDerivedFunctor R D E (dgModuleExtension R D E F)
    (fun _ hM => dgModuleExtension_homotopicallyProjective R D E F hM)
/-- 相対 tensor の実 graph 延長 ∞ 関手は完全。 -/
theorem dgModuleExtensionInfinity_isExactFunctor (F : DGFunctor R D E) :
    IsExactFunctor (dgModuleExtensionInfinity R D E F) :=
  dgModuleDerivedFunctor_isExactFunctor R D E _ _
end SerrePositivity.InfinityCategories
