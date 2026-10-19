module
public import SerrePositivity.InfinityCategories.Derived.StandardCofiberEdges
public import SerrePositivity.InfinityCategories.Derived.StandardCofiberVertexComparison
public import SerrePositivity.InfinityCategories.Stable.FunctorConjugationComparison

/-! # 標準 cofiber 三角形の像の第一・第二可換式

概要：D3 で写した標準 cofiber 列の二射を、元の鎖写像の Q 像と比較する。
方針：包含後の辺の計算を端点同定で輸送し、鎖写像に対する D3 の自然性を使う。
規約：実際の cofiber 列の頂点を保持する。使われ方：D7 の三角形同型。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
open scoped Simplicial ZeroObject
variable {S : Type u} [CommRing S] [HasDerivedCategory.{w} (ModuleCat.{u} S)]
variable {X Y : Semifree S}

/-- 標準 cofiber 列の第一射の導来比較。 -/
lemma derivedStandardCofiberTriangle_comm₁ (f : X.val ⟶ Y.val) :
    (derivedStableHomotopyEquivalence S).functor.map
        (semifreeCofiberZeroTriangle f).hoShortComplex.f ≫
      (derivedStandardCofiberMiddleIso f).hom =
    (derivedStandardCofiberSourceIso f).hom ≫ DerivedCategory.Q.map f := by
  obtain ⟨hx, hy, hf⟩ := (Arrow.mk_eq_mk_iff _ _).mp
    (semifreeCofiberZeroTriangle_f_arrow f)
  exact functor_conjugation_comparison _
    (eqToIso (congrArg SSet.HomotopyCategory.mk (semifreeCofiberZeroTriangle_vertex00 f)))
    (eqToIso (congrArg SSet.HomotopyCategory.mk (semifreeCofiberZeroTriangle_vertex10 f)))
    (derivedStableHomotopyEquivalenceVertexIso S X)
    (derivedStableHomotopyEquivalenceVertexIso S Y) _ _ _ hf
    (derivedStableHomotopyEquivalenceVertexIso_naturality S f)

/-- 標準 cofiber 列の第二射の導来比較。 -/
lemma derivedStandardCofiberTriangle_comm₂ (f : X.val ⟶ Y.val) :
    (derivedStableHomotopyEquivalence S).functor.map
        (semifreeCofiberZeroTriangle f).hoShortComplex.g ≫
      (derivedStandardCofiberTargetIso f).hom =
    (derivedStandardCofiberMiddleIso f).hom ≫
      DerivedCategory.Q.map (pushoutInclusionB f (0 : X.val ⟶ 0)) := by
  obtain ⟨hx, hy, hf⟩ := (Arrow.mk_eq_mk_iff _ _).mp
    (semifreeCofiberZeroTriangle_g_arrow f)
  exact functor_conjugation_comparison _
    (eqToIso (congrArg SSet.HomotopyCategory.mk (semifreeCofiberZeroTriangle_vertex10 f)))
    (eqToIso (congrArg SSet.HomotopyCategory.mk (semifreeCofiberZeroTriangle_vertex11 f)))
    (derivedStableHomotopyEquivalenceVertexIso S Y)
    (derivedStableHomotopyEquivalenceVertexIso S (semifreeCofiberZeroObject f)) _ _ _ hf
    (derivedStableHomotopyEquivalenceVertexIso_naturality S
      (X := Y) (Y := semifreeCofiberZeroObject f) (pushoutInclusionB f (0 : X.val ⟶ 0)))

end SerrePositivity.InfinityCategories
