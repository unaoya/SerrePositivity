module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Triangles.SuspensionShiftObjectComparison

/-! # D3 比較による懸垂と一回シフトの自然同型

概要：すべての h D(S) の対象と射に対し、懸垂の像と像の一回シフトを自然に比較する。
方針：頂点と dg 対象の標準同値で成分を輸送し、定値頂点上の自然性に帰着する。
規約：整数シフト全体の coherence は後続。使われ方：D7 の CommShift の生成同型。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (S : Type u) [CommRing S]

/-- 通常の h の対象をその頂点の semifree 複体で表す。 -/
def derivedStableObjectPresentation (x : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedStableHomotopyCategory S) : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv x.as.as

/-- 対象の標準表示の頂点は元の h の対象を復元する。 -/
lemma derivedStableObjectPresentation_vertex (x : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedStableHomotopyCategory S) :
    SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (derivedStableObjectPresentation S x)) = x := by
  apply SSet.Truncated.HomotopyCategory.ext
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.symm_apply_apply x.as.as

variable [HasDerivedCategory.{w} (ModuleCat.{u} S)]

/-- 懸垂と一回シフトの比較の全対象での成分。 -/
def derivedSuspensionShiftIsoApp (x : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedStableHomotopyCategory S) :
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedStableHomotopyEquivalence S).functor.obj
      ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionFunctor (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory S)).obj x) ≅
      ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedStableHomotopyEquivalence S).functor.obj x)⟦(1 : ℤ)⟧ :=
  eqToIso (congrArg (fun z => (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedStableHomotopyEquivalence S).functor.obj
      ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionFunctor (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory S)).obj z))
        (derivedStableObjectPresentation_vertex S x).symm) ≪≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSuspensionShiftObjectIso S (derivedStableObjectPresentation S x) ≪≫
    (shiftFunctor _ (1 : ℤ)).mapIso
      ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedStableHomotopyEquivalence S).functor.mapIso
        (eqToIso (derivedStableObjectPresentation_vertex S x)))

/-- 定値頂点上では標準 suspension による元の成分を保つ。 -/
lemma derivedSuspensionShiftIsoApp_vertex (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S) :
    derivedSuspensionShiftIsoApp S (SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X)) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSuspensionShiftObjectIso S X := by
  apply Iso.ext
  simp [derivedSuspensionShiftIsoApp, derivedStableObjectPresentation]
  rfl

/-- D3 比較は実際の懸垂と一回シフトを自然に比較する。 -/
def derivedSuspensionShiftIso :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionFunctor (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory S) ⋙ (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedStableHomotopyEquivalence S).functor ≅
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedStableHomotopyEquivalence S).functor ⋙ shiftFunctor _ (1 : ℤ) :=
  NatIso.ofComponents (derivedSuspensionShiftIsoApp S) (by
    intro x y f
    obtain ⟨v, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective x
    obtain ⟨w, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective y
    obtain ⟨X, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.symm.surjective v
    obtain ⟨Y, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.symm.surjective w
    change (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionFunctor (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory S) ⋙
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedStableHomotopyEquivalence S).functor).map f ≫
        (derivedSuspensionShiftIsoApp S (SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Y))).hom =
      (derivedSuspensionShiftIsoApp S (SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X))).hom ≫
        ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedStableHomotopyEquivalence S).functor ⋙ shiftFunctor _ (1 : ℤ)).map f
    rw [derivedSuspensionShiftIsoApp_vertex, derivedSuspensionShiftIsoApp_vertex]
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSuspensionShiftObjectIso_naturality S f)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
