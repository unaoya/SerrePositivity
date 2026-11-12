module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.RelativeHomCoherentNaturality
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PointedSpaceFiberVertices
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftPath
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PrismLiftSpace
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.RelativeFunctorExtensionSpace

/-!
概要：恒等射を始点に固定して、coherent な自然性の四角形を pointed-space 側へ持ち上げる。
方針：表現対象の恒等射の fiber 頂点を選び、二つの区間を順に left fibration で持ち上げる。
規約：始点・元の四角形・射と変換の全パラメーターを厳密に保つ。
使われ方：回収した変換と元の変換の二つの合成順序の終点を比較する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories

/-- 表現対象の自己相対 Hom の Kan 複体。 -/
def relativeHomIdentityKanObject {B : SSet.{u}} (q : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B) : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace q.val.hom q.val.hom, inferInstance⟩

/-- 自己 Hom の恒等射を表す、pointed-space 射影の fiber の実際の頂点。 -/
def relativeHomPointedIdentity {B : SSet.{u}} (q : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.spaceInfinityVertex (relativeHomIdentityKanObject q))) _⦋0⦌ :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceFiberVertexEquiv (relativeHomIdentityKanObject q)).symm
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorIdentity q.val).app (Opposite.op ⦋0⦌) PUnit.unit)

/-- 選んだ fiber の頂点は、元の相対恒等射そのものを表す。 -/
lemma relativeHomPointedIdentity_value {B : SSet.{u}} (q : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceFiberVertexEquiv (relativeHomIdentityKanObject q) (relativeHomPointedIdentity q) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorIdentity q.val).app (Opposite.op ⦋0⦌) PUnit.unit :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceFiberVertexEquiv (relativeHomIdentityKanObject q)).apply_symm_apply _

/-- 恒等射の点を任意の大きいパラメーター上で同じ定値の pointed 族にする。 -/
def relativeHomPointedIdentityFamily {B : SSet.{u}} (q : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B)
    (P : SSet.{u + 1}) : P ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PointedSpaceInfinity.{u} :=
  SSet.const (relativeHomPointedIdentity q) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.spaceInfinityVertex (relativeHomIdentityKanObject q))

/-- 恒等射の pointed 族は自己相対 Hom の頂点を厳密に被覆する。 -/
lemma relativeHomPointedIdentityFamily_projection {B : SSet.{u}}
    (q : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B) (P : SSet.{u + 1}) :
    relativeHomPointedIdentityFamily q P ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection =
      SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.spaceInfinityVertex (relativeHomIdentityKanObject q)) := by
  rw [relativeHomPointedIdentityFamily, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.comp_const]

/-- 同じ恒等射を使う pointed 族は任意のパラメーター制限に厳密に自然。 -/
lemma relativeHomPointedIdentityFamily_restrict {B : SSet.{u}}
    (q : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B) {P Q : SSet.{u + 1}} (k : P ⟶ Q) :
    k ≫ relativeHomPointedIdentityFamily q Q = relativeHomPointedIdentityFamily q P := by
  rw [relativeHomPointedIdentityFamily, relativeHomPointedIdentityFamily,
    ← Category.assoc, SSet.comp_const]

/-- 自然性の四角形の始点は、両パラメーターに定値な自己相対 Hom の頂点。 -/
lemma relativeHomCoherentNaturalitySquare_origin {B : SSet.{u}}
    (a q r : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeHomCoherentNaturalitySquare a q r =
      SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.spaceInfinityVertex (relativeHomIdentityKanObject q)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeHomCoherentNaturalitySquare_transformation_zero, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, Category.assoc]
  rw [← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _) (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeHomArrowPrism q r)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationCoherentEvaluation q.val), _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeHomArrowPrism_zero q r,
    SSet.const_comp, SSet.comp_const]
  congr 1
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityVertex_eq_coherent]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_vertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorEnrichedEvaluation q.val) q


/-- 二つの区間の最初の頂点を、同じパラメーターを保って含める。 -/
def squarePrismOrigin (P : SSet.{u}) : P ⟶ (Δ[1] : SSet.{u}) ⊗ (Δ[1] ⊗ P) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 P ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[1] ⊗ P)

/-- 四角形の族の始点包含は left anodyne。 -/
lemma squarePrismOrigin_leftAnodyne (P : SSet.{u}) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions (squarePrismOrigin P) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions.comp_mem _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.prismEndpoint_zero_leftAnodyne P)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.prismEndpoint_zero_leftAnodyne (Δ[1] ⊗ P))

/-- left fibration の四角形の族は、始点の lift を厳密に保って全体へ持ち上がる。 -/
lemma leftFibration_lift_square_origin {P E X : SSet.{u}}
    (p : E ⟶ X) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (s : P ⟶ E)
    (R : (Δ[1] : SSet.{u}) ⊗ (Δ[1] ⊗ P) ⟶ X)
    (hs : s ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 P ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[1] ⊗ P) ≫ R) :
    ∃ W : (Δ[1] : SSet.{u}) ⊗ (Δ[1] ⊗ P) ⟶ E,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 P ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[1] ⊗ P) ≫ W = s ∧ W ≫ p = R := by
  obtain ⟨v, hv, hvp⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibration_lift_prism p s
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[1] ⊗ P) ≫ R) hs
  obtain ⟨W, hW, hWp⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibration_lift_prism p v R hvp
  refine ⟨W, ?_, hWp⟩
  rw [hW, hv]

/-- 恒等射と元の自然性の四角形を厳密に固定する、全 pointed lift の空間。 -/
def relativeHomPointedNaturalitySpace {B : SSet.{u}} (a q r : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B) :
    SSet.{u + 1} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpace _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeHomCoherentNaturalitySquare a q r)
    (squarePrismOrigin _) (relativeHomPointedIdentityFamily q _) (by
      rw [relativeHomPointedIdentityFamily_projection]
      simpa only [squarePrismOrigin, Category.assoc] using
        (relativeHomCoherentNaturalitySquare_origin a q r).symm)

/-- 始点固定の pointed 自然性の持ち上げ空間は、全高次を含め可縮な Kan 複体。 -/
lemma relativeHomPointedNaturalitySpace_isContractibleKan {B : SSet.{u}}
    (a q r : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (relativeHomPointedNaturalitySpace a q r) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpace_isContractibleKan _ _ _ (squarePrismOrigin_leftAnodyne _) _ _

/-- 可縮な持ち上げ空間の頂点は、実際の始点固定の pointed 四角形と全単射に対応する。 -/
def relativeHomPointedNaturalitySpaceVertexEquiv {B : SSet.{u}} (a q r : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B) :
    {W : _ ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PointedSpaceInfinity.{u} //
      W ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection = _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeHomCoherentNaturalitySquare a q r ∧
        squarePrismOrigin _ ≫ W = relativeHomPointedIdentityFamily q _} ≃
    (relativeHomPointedNaturalitySpace a q r) _⦋0⦌ :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpaceVertexEquiv _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection
    (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeHomCoherentNaturalitySquare a q r) (squarePrismOrigin _)
    (relativeHomPointedIdentityFamily q _) (by
      rw [relativeHomPointedIdentityFamily_projection]
      simpa only [squarePrismOrigin, Category.assoc] using
        (relativeHomCoherentNaturalitySquare_origin a q r).symm)

/-- 自然性の四角形全体を、同じ可縮な選択空間から始点固定で持ち上げる。 -/
lemma exists_relativeHomPointedNaturalitySquare {B : SSet.{u}}
    (a q r : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B) :
    ∃ W : _ ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PointedSpaceInfinity.{u},
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ W = relativeHomPointedIdentityFamily q _ ∧
      W ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection = _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeHomCoherentNaturalitySquare a q r := by
  obtain ⟨x⟩ := (relativeHomPointedNaturalitySpace_isContractibleKan a q r).nonempty
  let W := (relativeHomPointedNaturalitySpaceVertexEquiv a q r).symm x
  refine ⟨W.val, ?_, W.property.1⟩
  simpa only [squarePrismOrigin, Category.assoc] using W.property.2

/-- 同じ pointed 四角形から取り出した三角形は、元の自然性の三角形を厳密に被覆する。 -/
lemma relativeHomPointedNaturalityTriangle_projection {B : SSet.{u}}
    (a q r : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B) (W : _ ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PointedSpaceInfinity.{u})
    (hW : W ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection = _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeHomCoherentNaturalitySquare a q r) (i : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.squarePrismTriangle W i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection =
      _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeHomCoherentNaturalityTriangle a q r i := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.squarePrismTriangle, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeHomCoherentNaturalityTriangle, Category.assoc, hW]

/-- 始点固定の一つの pointed 四角形は、同じ長辺を持つ二つの実際の三角形を与える。 -/
lemma exists_relativeHomPointedNaturalityTriangles {B : SSet.{u}}
    (a q r : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B) :
    ∃ W : _ ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PointedSpaceInfinity.{u},
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ W = relativeHomPointedIdentityFamily q _ ∧
      W ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection = _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeHomCoherentNaturalitySquare a q r ∧
      (∀ i, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.squarePrismTriangle W i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection =
        _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeHomCoherentNaturalityTriangle a q r i) ∧
      (stdSimplex.δ (1 : Fin 3) ▷ _) ≫ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.squarePrismTriangle W 0 =
        (stdSimplex.δ (1 : Fin 3) ▷ _) ≫ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.squarePrismTriangle W 1 := by
  obtain ⟨W, h₀, hp⟩ := exists_relativeHomPointedNaturalitySquare a q r
  refine ⟨W, h₀, hp, fun i ↦ relativeHomPointedNaturalityTriangle_projection a q r W hp i, ?_⟩
  rw [_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.squarePrismTriangle_diagonal, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.squarePrismTriangle_diagonal]

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories
