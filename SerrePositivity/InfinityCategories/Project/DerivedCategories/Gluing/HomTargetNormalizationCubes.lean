module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomTargetIdentityComma
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomTargetNormalizedPrism
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomMappingModel
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.NormalizationCubeIntervalFaces
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.NativeNormalizationPasting
/-!
概要：元終域 E で元 Hom 入力を保持する二つの実正規化 cube と共有面を構成する。
方針：元恒等 comma 関手の Hom 全族を一般正規化へ渡し、共有面で貼り合わせる。
規約：元面・係数面・側面を同時に保持する。導来加群値を経由しない。
使われ方：lax Hom 比較を元二作用の係数 path 比較へ相対的に移す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory DifferentialGraded SSet KST.SConstruction
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R]
  (C D E : Type (max (u + 1) v)) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
  (p : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C E) (q : _root_.SerrePositivity.DifferentialGraded.DGFunctor R D E)
  (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D (dgHomGluingBimodule R C D E p q))
local notation "M" => dgHomGluingBimodule R C D E p q
local notation "Q" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R E E (DGFunctor.id E)
local notation "IX" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetIdentityCommaObject R C D E p q X
local notation "IY" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetIdentityCommaObject R C D E p q Y

def dgGluingHomTargetNormalizationHomInput : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, max (u + 1) v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComplex R C D M X Y)) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R Q IX IY :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomMappingIso R C D M X Y).inv ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (D := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) (E := Q)
      (x := X) (y := Y) (x' := IX) (y' := IY)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetIdentityCommaFunctor R C D E p q).map X Y)

section
attribute [local irreducible] dgHomGluingBimodule

/-- 正規化後の全 Hom 入力は、元二作用と第三 cochain を持つ同じ実入力。 -/
lemma dgGluingHomTargetNormalizationHomInput_normalized :
    dgGluingHomTargetNormalizationHomInput R C D E p q X Y ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (D := Q) (E := Q)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaNormalizeHom R E IX IY) =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetNormalizedRawPinchedInput R C D E p q X Y := by
  rw [dgGluingHomTargetNormalizationHomInput, Category.assoc,
    ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap_comp,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetIdentityCommaFunctor_normalized]
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedModelInverse_naturality
    (C := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) (D := Q)
    (x := X) (y := Y)
    (x' := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E (p.obj X.left))
    (y' := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E (q.obj Y.right))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetNormalizedHom R C D E p q X Y)).symm

end

def dgGluingHomTargetPreNormalizeCube :
    (Δ[1] : SSet.{max (u + 1) v}) ⊗ (Δ[1] ⊗ (Δ[1] ⊗ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, max (u + 1) v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComplex R C D M X Y)))) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaPreNormalizeCube.{u, max (u + 1) v} R E IX IY
      (dgGluingHomTargetNormalizationHomInput R C D E p q X Y) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R E)

def dgGluingHomTargetPostNormalizeCube :
    (Δ[1] : SSet.{max (u + 1) v}) ⊗ (Δ[1] ⊗ (Δ[1] ⊗ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, max (u + 1) v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComplex R C D M X Y)))) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaPostNormalizeCube.{u, max (u + 1) v} R E IX IY
      (dgGluingHomTargetNormalizationHomInput R C D E p q X Y) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R E)

lemma dgGluingHomTargetNormalizationCube_shared_face :
    (Δ[1] ◁ (Δ[1] ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, max (u + 1) v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComplex R C D M X Y)))) ≫
      dgGluingHomTargetPreNormalizeCube R C D E p q X Y =
    (Δ[1] ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[1] ⊗ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, max (u + 1) v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComplex R C D M X Y)))) ≫
      dgGluingHomTargetPostNormalizeCube R C D E p q X Y := by
  have h := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaPreNormalizeCube_interval_zero R E IX IY
    (dgGluingHomTargetNormalizationHomInput R C D E p q X Y)).trans
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaPostNormalizeCube_source R E IX IY
        (dgGluingHomTargetNormalizationHomInput R C D E p q X Y)).symm
  have h' := congrArg (fun k => k ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R E)) h
  simpa only [dgGluingHomTargetPreNormalizeCube, dgGluingHomTargetPostNormalizeCube,
    Category.assoc] using h'

def dgGluingHomTargetNormalizationPasting :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNormalizationPasting
    (dgGluingHomTargetPreNormalizeCube R C D E p q X Y)
    (dgGluingHomTargetPostNormalizeCube R C D E p q X Y)
    (dgGluingHomTargetNormalizationCube_shared_face R C D E p q X Y)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
