module
public import SerrePositivity.KST.SConstruction.DGFunctorNativeStrictEdgeComparison
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConeEndTriangle
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.TruncatedTriangles

/-!
概要：元 cone 全 end 二単体の二短辺を、旧厳密変換の同じ全関手辺へ接続する。
方針：元二単体の面回収と全 end 辺の native 評価の厳密一致を使う。
規約：元全二単体と次数 −1 primitive を変更しない。
使われ方：同じ元 cofiber 全図式と LT 逆回転の指定境界比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalClosed SSet DifferentialGraded InfinityCategories
open scoped Simplicial

/-- 概要：同じ元 cone 全二単体の最初の辺は元厳密変換の指定ホモトピー辺。
方針：元第一面を全 native 評価へ送る。
規約：全写像空間の辺等号。使われ方：元 counit 側の指定境界。 -/
lemma dgModuleNaturalConeFullTriangle_firstEdge (R : Type u) [CommRing R] (D P : Type (u + 1))
    [DGCategory R D] [Small.{u} D] [DGCategory R P] [Small.{u} P]
    (F G : DGFunctor R P (RightModule R D)) (η : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G) :
    ((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R P)).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))).δ 2
      ((dgFunctorNativeFullFamilyMap R P (RightModule R D)).app (Opposite.op ⦋2⦌)
        (dgModuleNaturalConeEndTriangle R D F G η)) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy η.homotopy).edge := by
  have hf : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (DGFunctor R P (RightModule R D))).δ 2
      (dgModuleNaturalConeEndTriangle R D F G η) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ofEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pairObj F G)
        (dgStrictNatTransEndCycle R P (RightModule R D) η) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.triangle_face01 (dgModuleNaturalConeEndTriangleData R D F G η)
  have hn := SSet.δ_naturality_apply
    (dgFunctorNativeFullFamilyMap R P (RightModule R D)) 2
    (dgModuleNaturalConeEndTriangle R D F G η)
  exact hn.symm.trans ((congrArg
    ((dgFunctorNativeFullFamilyMap R P (RightModule R D)).app (Opposite.op ⦋1⦌)) hf).trans
      (dgFunctorNativeStrictNatTrans_edge R P (RightModule R D) η))

/-- 概要：同じ元 cone 全二単体の第二の辺は元 cone 包含の指定ホモトピー辺。
方針：元第二面を同じ全 native 評価へ送る。
規約：全二単体を選び直さない。使われ方：元 cofiber 側の指定境界。 -/
lemma dgModuleNaturalConeFullTriangle_lastEdge (R : Type u) [CommRing R]
    (D P : Type (u + 1)) [DGCategory R D] [Small.{u} D] [DGCategory R P] [Small.{u} P]
    (F G : DGFunctor R P (RightModule R D)) (η : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G) :
    ((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R P)).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))).δ 0
      ((dgFunctorNativeFullFamilyMap R P (RightModule R D)).app (Opposite.op ⦋2⦌)
        (dgModuleNaturalConeEndTriangle R D F G η)) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (dgModuleNaturalConeInr R D F G η).homotopy).edge := by
  have hf : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (DGFunctor R P (RightModule R D))).δ 0
      (dgModuleNaturalConeEndTriangle R D F G η) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ofEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pairObj G (dgModuleNaturalConeFunctor R D F G η))
        (dgStrictNatTransEndCycle R P (RightModule R D) (dgModuleNaturalConeInr R D F G η)) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.triangle_face12 (dgModuleNaturalConeEndTriangleData R D F G η)
  have hn := SSet.δ_naturality_apply
    (dgFunctorNativeFullFamilyMap R P (RightModule R D)) 0
    (dgModuleNaturalConeEndTriangle R D F G η)
  exact hn.symm.trans ((congrArg
    ((dgFunctorNativeFullFamilyMap R P (RightModule R D)).app (Opposite.op ⦋1⦌)) hf).trans
      (dgFunctorNativeStrictNatTrans_edge R P (RightModule R D) (dgModuleNaturalConeInr R D F G η)))

end SerrePositivity.KST.SConstruction
