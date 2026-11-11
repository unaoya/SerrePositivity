module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNuNullCompositeVertices

/-!
概要：指定商比較の零 Hom 因子分解と元両下三角形の合成端を貼り合わせる。
方針：全 Hom の最大 path の回収式と同じ二端点の式を使う。
規約：同じ零成分内の厳密等号。使われ方：元二胞体付き混合境界の相対延長。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R) (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d)
local notation "K" => dgKInputStableValue R (dgOdotMilnorFlatKernelInput R d)
local notation "B" => dgKInputStableValue R (dgOdotMilnorResolvedInput R d)

/-- 概要：指定商比較の零端点は元実下三角形の同じ最大合成頂点。
方針：同じ実合成の二つの厳密回収式を零成分の包含で照合する。
規約：元 path と元比較辺の端点を保持。使われ方：混合境界の実面側の貼り合わせ。 -/
lemma dgOdotMilnorNuProjectionNullFactor_source :
    (dgOdotMilnorNuProjectionNullFactor R d h).app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      (dgOdotMilnorNuNullTriangleFactor R d 1).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex dgOdotMilnorNuNullUpperMaximalPath.{u}) := by
  apply Subtype.ext
  exact (dgOdotMilnorNuProjectionNullHom_source R d h).trans
    (congrArg (fun x =>
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors (K) (B) : SSet.{u + 1})).ι.app
        (Opposite.op ⦋0⦌) x) (dgOdotMilnorNuNullLowerHom_maximal R d)).symm

/-- 概要：指定商比較の一端点は同じ絶対下三角形の元最大合成頂点。
方針：元完備化後射影との同じ合成の厳密回収を使う。
規約：元絶対二胞体を保持。使われ方：混合境界の絶対面側の貼り合わせ。 -/
lemma dgOdotMilnorNuProjectionNullFactor_target :
    (dgOdotMilnorNuProjectionNullFactor R d h).app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
      (dgOdotMilnorNuAbsoluteTriangleFactor R d h 1).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex dgOdotMilnorNuNullUpperMaximalPath.{u}) := by
  apply Subtype.ext
  exact (dgOdotMilnorNuProjectionNullHom_target R d h).trans
    (congrArg (fun x =>
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors (K) (B) : SSet.{u + 1})).ι.app
        (Opposite.op ⦋0⦌) x) (dgOdotMilnorNuAbsoluteLowerHom_maximal R d h)).symm

end SerrePositivity.KST.SConstruction
