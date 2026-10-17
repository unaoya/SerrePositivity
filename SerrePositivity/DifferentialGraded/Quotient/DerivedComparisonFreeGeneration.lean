module
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonFreeExtension
public import SerrePositivity.DifferentialGraded.Verdier.DerivedGeneratorInduction
public import SerrePositivity.DifferentialGraded.Derived.FunctorExtensionTriangles
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonFlatness
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonPathModule

/-! # 自由右加群の導来像の局所生成

一対象環からの導来延長と代表加群による帰納法を接続する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- b の代表加群を含む localizing な性質は、一対象環からの全導来延長の像を含む。 -/
lemma pointDerivedExtension_mem
    (P : ObjectProperty (DerivedModuleCategory A D)) [P.IsTriangulated]
    [P.IsClosedUnderIsomorphisms]
    (hcoprod : ∀ (I : Type u) (G : I → DerivedModuleCategory A D),
      (∀ i, P (G i)) → P (∐ G)) (b : D)
    (hb : P ((moduleToDerived A D).obj (ForgetEnrichment.of (Complex A) (representable A b))))
    (X : DerivedModuleCategory A PUnit.{1}) :
    P ((dgDerivedExtension A PUnit.{1} D (pointDGFunctor A D b)).obj X) := by
  let := dgDerivedExtensionCommShift A PUnit.{1} D (pointDGFunctor A D b)
  let := dgDerivedExtensionIsTriangulated A PUnit.{1} D (pointDGFunctor A D b)
  let := (dgDerivedExtensionRestrictionAdjunction A PUnit.{1} D
    (pointDGFunctor A D b)).isLeftAdjoint
  apply moduleDerived_functor_generatorInduction A PUnit.{1} D
    (dgDerivedExtension A PUnit.{1} D (pointDGFunctor A D b)) P hcoprod
    (fun _ => inferInstance) _ X
  intro x
  cases x
  exact P.prop_of_iso (dgDerivedExtensionRepresentableIso A PUnit.{1} D
    (pointDGFunctor A D b) PUnit.unit).symm hb

/-- K-flat 係数の自由加群へ compact 対象から向かう射は S 上の有限 cell を経由する。 -/
lemma freeAtKFlat_finiteCellFactorTarget (S : Set D) (b : D) (hb : b ∈ S)
    (K : Complex A) (hK : complexKFlat A K) :
    moduleFiniteCellFactorTarget A D S ((moduleToDerived A D).obj ((freeAt b).obj K)) := by
  have hrep : moduleFiniteCellFactorTarget A D S
      ((moduleToDerived A D).obj (ForgetEnrichment.of (Complex A) (representable A b))) :=
    moduleFiniteCellFactorTarget_of_finiteCell A D
      ((moduleFiniteCellOver A D S).prop_map_obj (moduleToDerived A D)
        (moduleFiniteCellOver_representable A D b hb))
  exact (moduleFiniteCellFactorTarget A D S).prop_of_iso (derivedFreeAtKFlatIso A D b K hK)
    (pointDerivedExtension_mem A D (moduleFiniteCellFactorTarget A D S)
      (fun _ G hG => moduleFiniteCellFactorTarget_coproduct A D G hG) b hrep
      ((moduleToDerived A PUnit.{1}).obj (ForgetEnrichment.of (Complex A) (ringModule A K))))

/-- 一対象環の通常の射影置換を評価して、任意の複体の K-flat 置換を得る。 -/
lemma exists_coefficientKFlat_resolution (K : Complex A) :
    ∃ (P : Complex A) (q : P ⟶ K), complexKFlat A P ∧ QuasiIso q := by
  let M := ForgetEnrichment.of (Complex A) (ringModule A K)
  let P := moduleCanonicalProjectiveResolution A PUnit.{1} M
  refine ⟨(moduleEvaluation A PUnit.{1} PUnit.unit).obj P.obj,
    (moduleEvaluation A PUnit.{1} PUnit.unit).map P.π, ?_, P.quasiIso PUnit.unit⟩
  intro L hL
  have hp := moduleHomotopicallyProjective_relativeKFlat A PUnit.{1} P.projective
    (ringLeftModule A L) (fun _ => hL)
  exact cochainAcyclic_of_iso hp
    (BalancedTensor.ringIso A (ForgetEnrichment.to (Complex A) P.obj) (ringLeftModule A L))

/-- 代表加群の値が K-flat なら、自由加群関手は係数の擬同型を保つ。 -/
lemma freeAt_quasiIso_of_homKFlat (b : D)
    (hb : ∀ x : D, complexKFlat A (homObject A D x b))
    {K L : Complex A} (q : K ⟶ L) [QuasiIso q] :
    moduleQuasiIso A D ((freeAt b).map q) := by
  intro x
  change QuasiIso ((moduleEvaluation A D x).map (tensorModuleMap q (representable A b)))
  rw [tensorModuleMap_eval]
  exact complexKFlat_quasiIso_left A (hb x) q

/-- 入る側の局所 K-flat 性の下では、係数複体を任意に取れる。 -/
lemma freeAt_finiteCellFactorTarget_into (S : Set D) (h : homIntoKFlat A D S)
    (b : S) (K : Complex A) :
    moduleFiniteCellFactorTarget A D S ((moduleToDerived A D).obj ((freeAt b.val).obj K)) := by
  obtain ⟨P, q, hP, hq⟩ := exists_coefficientKFlat_resolution A K
  have := hq
  exact (moduleFiniteCellFactorTarget A D S).prop_of_iso
    (moduleDerivedIso A D ((freeAt b.val).map q)
      (freeAt_quasiIso_of_homKFlat A D b.val (fun x => h x b) q))
    (freeAtKFlat_finiteCellFactorTarget A D S b.val b.property P hP)

/-- 片側局所 K-flat 仮定の下で、全ての正の path 項は S による有限因子分解性を持つ。 -/
lemma positivePath_finiteCellFactorTarget (S : Set D) (h : localKFlat A D S)
    (b : S) (w : Word S) (z : D) :
    moduleFiniteCellFactorTarget A D S ((moduleToDerived A D).obj
      (ForgetEnrichment.of (Complex A) (pathModule A D (b :: w) z))) := by
  apply (moduleFiniteCellFactorTarget A D S).prop_of_iso
    ((moduleToDerived A D).mapIso (pathModuleFreeIso A D b w z)).symm
  rcases h with h | h
  · exact freeAt_finiteCellFactorTarget_into A D S h b (pathSuffixWeight A D w b z)
  · exact freeAtKFlat_finiteCellFactorTarget A D S b.val b.property
      (pathSuffixWeight A D w b z) (pathSuffixWeight_kFlat A D h w b z)

/-- M9 の次数零 flat Hom からも、同じ正の path の有限因子分解性を供給できる。 -/
lemma positivePath_finiteCellFactorTarget_of_flat_zero
    (hz : ∀ (x y : D) (i : ℤ), i ≠ 0 → IsZero ((homObject A D x y).X i))
    (hf : ∀ x y : D, Module.Flat A ((homObject A D x y).X 0))
    (S : Set D) (b : S) (w : Word S) (z : D) :
    moduleFiniteCellFactorTarget A D S ((moduleToDerived A D).obj
      (ForgetEnrichment.of (Complex A) (pathModule A D (b :: w) z))) :=
  positivePath_finiteCellFactorTarget A D S
    (Or.inl (allHomKFlat_into A D (allHomKFlat_of_flat_zero A D hz hf) S)) b w z

end SerrePositivity.DifferentialGraded.DGQuotient
