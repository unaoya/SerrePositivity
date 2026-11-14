module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FiberCofiber.StandardCofiberEdges
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FiberCofiber.StandardCofiberVertexComparison
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.FunctorConjugationComparison

/-! # 標準 cofiber 三角形の像の第一・第二可換式

概要：D3 で写した標準 cofiber 列の二射を、元の鎖写像の Q 像と比較する。
方針：包含後の辺の計算を端点同定で輸送し、鎖写像に対する D3 の自然性を使う。
規約：実際の cofiber 列の頂点を保持する。使われ方：D7 の三角形同型。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial ZeroObject
variable {S : Type u} [CommRing S] [HasDerivedCategory.{w} (ModuleCat.{u} S)]
variable {X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S}

/-- 標準 cofiber 列の第一射の導来比較。 -/
lemma derivedStandardCofiberTriangle_comm₁ (f : X.val ⟶ Y.val) :
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedStableHomotopyEquivalence S).functor.map
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberZeroTriangle f).hoShortComplex.f ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedStandardCofiberMiddleIso f).hom =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedStandardCofiberSourceIso f).hom ≫ DerivedCategory.Q.map f := by
  obtain ⟨hx, hy, hf⟩ := (Arrow.mk_eq_mk_iff _ _).mp
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberZeroTriangle_f_arrow f)
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.functor_conjugation_comparison _
    (eqToIso (congrArg SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberZeroTriangle_vertex00 f)))
    (eqToIso (congrArg SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberZeroTriangle_vertex10 f)))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedStableHomotopyEquivalenceVertexIso S X)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedStableHomotopyEquivalenceVertexIso S Y) _ _ _ hf
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedStableHomotopyEquivalenceVertexIso_naturality S f)

/-- 標準 cofiber 列の第二射の導来比較。 -/
lemma derivedStandardCofiberTriangle_comm₂ (f : X.val ⟶ Y.val) :
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedStableHomotopyEquivalence S).functor.map
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberZeroTriangle f).hoShortComplex.g ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedStandardCofiberTargetIso f).hom =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedStandardCofiberMiddleIso f).hom ≫
      DerivedCategory.Q.map (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.pushoutInclusionB f (0 : X.val ⟶ 0)) := by
  obtain ⟨hx, hy, hf⟩ := (Arrow.mk_eq_mk_iff _ _).mp
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberZeroTriangle_g_arrow f)
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.functor_conjugation_comparison _
    (eqToIso (congrArg SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberZeroTriangle_vertex10 f)))
    (eqToIso (congrArg SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberZeroTriangle_vertex11 f)))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedStableHomotopyEquivalenceVertexIso S Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedStableHomotopyEquivalenceVertexIso S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberZeroObject f)) _ _ _ hf
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedStableHomotopyEquivalenceVertexIso_naturality S
      (X := Y) (Y := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberZeroObject f) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.pushoutInclusionB f (0 : X.val ⟶ 0)))

end SerrePositivity.InfinityCategories.Project.DerivedCategories
