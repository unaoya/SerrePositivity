module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetIdentityComma
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetNormalizedPrism
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomMappingModel
public import SerrePositivity.InfinityCategories.Derived.Gluing.NormalizationCubeIntervalFaces
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativeNormalizationPasting
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory DifferentialGraded DGNerve SSet KST.SConstruction
open scoped Simplicial
variable (R : Type u) [CommRing R]
  (C D E : Type (max (u + 1) v)) [DGCategory R C] [Small.{u} C]
  [DGCategory R D] [DGCategory R E] [Small.{u} E]
  (p : DGFunctor R C E) (q : DGFunctor R D E)
  (X Y : DGGluingObject R C D (dgHomGluingBimodule R C D E p q))
local notation "M" => dgHomGluingBimodule R C D E p q
local notation "Q" => DGFunctorCommaObject R E E (DGFunctor.id E)
local notation "IX" => dgGluingHomTargetIdentityCommaObject R C D E p q X
local notation "IY" => dgGluingHomTargetIdentityCommaObject R C D E p q Y

def dgGluingHomTargetNormalizationHomInput : (complexPinchedSpace.{u, max (u + 1) v} (dgGluingHomComplex R C D M X Y)) ⟶ DGNerve.pinchedHom R Q IX IY :=
  (dgGluingHomMappingIso R C D M X Y).inv ≫
    pinchedHomChainMap (D := DGGluingObject R C D M) (E := Q)
      (x := X) (y := Y) (x' := IX) (y' := IY)
      ((dgGluingHomTargetIdentityCommaFunctor R C D E p q).map X Y)

section
attribute [local irreducible] dgHomGluingBimodule

/-- 正規化後の全 Hom 入力は、元二作用と第三 cochain を持つ同じ実入力。 -/
lemma dgGluingHomTargetNormalizationHomInput_normalized :
    dgGluingHomTargetNormalizationHomInput R C D E p q X Y ≫
      pinchedHomChainMap (D := Q) (E := Q)
        (dgGluingIdentityCommaNormalizeHom R E IX IY) =
    dgGluingHomTargetNormalizedRawPinchedInput R C D E p q X Y := by
  rw [dgGluingHomTargetNormalizationHomInput, Category.assoc,
    ← pinchedHomChainMap_comp,
    dgGluingHomTargetIdentityCommaFunctor_normalized]
  exact (dgGluingComplexPinchedModelInverse_naturality
    (C := DGGluingObject R C D M) (D := Q)
    (x := X) (y := Y)
    (x' := dgGluingIdentityCommaObject R E (p.obj X.left))
    (y' := dgGluingIdentityCommaObject R E (q.obj Y.right))
    (dgGluingHomTargetNormalizedHom R C D E p q X Y)).symm

end

def dgGluingHomTargetPreNormalizeCube :
    (Δ[1] : SSet.{max (u + 1) v}) ⊗ (Δ[1] ⊗ (Δ[1] ⊗ (complexPinchedSpace.{u, max (u + 1) v} (dgGluingHomComplex R C D M X Y)))) ⟶ dgNerve R E :=
  dgGluingIdentityCommaPreNormalizeCube.{u, max (u + 1) v} R E IX IY
      (dgGluingHomTargetNormalizationHomInput R C D E p q X Y) ≫
    dgNerve.map (dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R E)

def dgGluingHomTargetPostNormalizeCube :
    (Δ[1] : SSet.{max (u + 1) v}) ⊗ (Δ[1] ⊗ (Δ[1] ⊗ (complexPinchedSpace.{u, max (u + 1) v} (dgGluingHomComplex R C D M X Y)))) ⟶ dgNerve R E :=
  dgGluingIdentityCommaPostNormalizeCube.{u, max (u + 1) v} R E IX IY
      (dgGluingHomTargetNormalizationHomInput R C D E p q X Y) ≫
    dgNerve.map (dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R E)

lemma dgGluingHomTargetNormalizationCube_shared_face :
    (Δ[1] ◁ (Δ[1] ◁ prismEndpoint 0 (complexPinchedSpace.{u, max (u + 1) v} (dgGluingHomComplex R C D M X Y)))) ≫
      dgGluingHomTargetPreNormalizeCube R C D E p q X Y =
    (Δ[1] ◁ prismEndpoint 0 (Δ[1] ⊗ (complexPinchedSpace.{u, max (u + 1) v} (dgGluingHomComplex R C D M X Y)))) ≫
      dgGluingHomTargetPostNormalizeCube R C D E p q X Y := by
  have h := (dgGluingIdentityCommaPreNormalizeCube_interval_zero R E IX IY
    (dgGluingHomTargetNormalizationHomInput R C D E p q X Y)).trans
      (dgGluingIdentityCommaPostNormalizeCube_source R E IX IY
        (dgGluingHomTargetNormalizationHomInput R C D E p q X Y)).symm
  have h' := congrArg (fun k => k ≫
    dgNerve.map (dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R E)) h
  simpa only [dgGluingHomTargetPreNormalizeCube, dgGluingHomTargetPostNormalizeCube,
    Category.assoc] using h'

def dgGluingHomTargetNormalizationPasting :=
  dgGluingNormalizationPasting
    (dgGluingHomTargetPreNormalizeCube R C D E p q X Y)
    (dgGluingHomTargetPostNormalizeCube R C D E p q X Y)
    (dgGluingHomTargetNormalizationCube_shared_face R C D E p q X Y)

end SerrePositivity.InfinityCategories
