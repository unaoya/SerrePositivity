module
public import SerrePositivity.KST.SConstruction.DGModuleExtensionIdentity
public import SerrePositivity.DifferentialGraded.Tensor.UnitBimoduleIso

/-! # 実恒等延長の全 Hom 自然な tensor 単位同型
概要：元の恒等延長の単位比較を、全加群を左パラメータとする双加群同型へ束ねる。
方針：対角との等号移送と元の tensor 左単位を合成し、元の対象別同型を回収する。
規約：大きい全加群型の smallness を仮定しない。使われ方：実 Perf 比較の三角整合性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 対角との等号を保持した、全加群上の元の左 tensor 単位同型。 -/
def dgDiagonalTensorUnitIso (Q : Bimodule A D D) (h : Q = Bimodule.diagonal A D) :
    BimoduleCategory.of A D (RightModule A D)
        (BimoduleTensor.compose A D D (RightModule A D) Q (DGFunctor.id _)) ≅
      BimoduleCategory.of A D (RightModule A D) (DGFunctor.id _) :=
  eqToIso (congrArg (fun P => BimoduleCategory.of A D (RightModule A D)
    (BimoduleTensor.compose A D D (RightModule A D) P (DGFunctor.id _))) h) ≪≫
      BimoduleTensor.leftBimoduleUnitIso A D (RightModule A D) (DGFunctor.id _)

/-- 全加群上の単位同型は、元の対象別の等号移送を保つ単位同型を回収する。 -/
lemma dgDiagonalTensorUnitIso_evaluation (Q : Bimodule A D D)
    (h : Q = Bimodule.diagonal A D) (M : RightModule A D) :
    (BimoduleCategory.evaluation A D (RightModule A D) M).mapIso
        (dgDiagonalTensorUnitIso A D Q h) = dgDiagonalTensorUnitAt A D Q h M := by
  subst Q
  simp only [dgDiagonalTensorUnitIso, eqToIso_refl, Iso.refl_trans]
  rfl

/-- 元の厳密な恒等 dg 入力の、全 Hom 自然な実 tensor 単位同型。 -/
def dgModuleExtensionIdentityTensorIso :
    BimoduleCategory.of A D (RightModule A D)
        (dgModuleExtension A D D (DGFunctor.id D)) ≅
      BimoduleCategory.of A D (RightModule A D) (DGFunctor.id _) :=
  dgDiagonalTensorUnitIso A D _ (functorGraph_identity A D)

/-- 実 tensor 単位同型の評価は、以前の同じ実恒等延長の単位比較。 -/
lemma dgModuleExtensionIdentityTensorIso_evaluation (M : RightModule A D) :
    (BimoduleCategory.evaluation A D (RightModule A D) M).mapIso
        (dgModuleExtensionIdentityTensorIso A D) = dgModuleExtensionIdentityAt A D M :=
  dgDiagonalTensorUnitIso_evaluation A D _ (functorGraph_identity A D) M

end SerrePositivity.KST.SConstruction
