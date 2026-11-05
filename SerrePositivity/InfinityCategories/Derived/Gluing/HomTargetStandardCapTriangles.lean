module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetIdentityCommaProjections
public import SerrePositivity.InfinityCategories.Derived.Gluing.NormalizationUnitCaps
public import SerrePositivity.InfinityCategories.Derived.Gluing.DGCompositionTriangleParameterNaturality
/-!
概要：元終域の単位 cap の標準端は、同じ元二作用の標準合成三角形である。
方針：元 Hom 鎖射影を保つ二射影式と全三角形のパラメーター自然性を使う。
規約：三辺だけでなく全三角形を同定する。使われ方：元入力付き補正道の標準端。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory DifferentialGraded DGNerve SSet KST.SConstruction
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R]
  (C D E : Type (max (u + 1) v)) [DGCategory R C] [Small.{u} C]
  [DGCategory R D] [DGCategory R E] [Small.{u} E]
  (p : DGFunctor R C E) (q : DGFunctor R D E)
  (X Y : DGGluingObject R C D (dgHomGluingBimodule R C D E p q))
local notation "M" => dgHomGluingBimodule R C D E p q
local notation "IX" => dgGluingHomTargetIdentityCommaObject R C D E p q X
local notation "IY" => dgGluingHomTargetIdentityCommaObject R C D E p q Y
attribute [local irreducible] dgHomGluingBimodule

lemma dgGluingHomTargetPreCapTriangle_one_standard :
    (Δ[2] ◁ (ι₁ : complexPinchedSpace.{u, max (u + 1) v}
      (dgGluingHomComplex R C D M X Y) ⟶ _)) ≫
      dgGluingPreUnitCapTriangleFamily.{u, max (u + 1) v} R E IX IY
        (dgGluingHomTargetNormalizationHomInput R C D E p q X Y) =
    (Δ[2] ◁ complexPinchedMap.{u, max (u + 1) v} (dgGluingRightHomMap R C D M X Y)) ≫
      dgGluingHomTargetRightCompositionTriangle R C D E p q X Y := by
  have h := dgGluingPreUnitCapTriangleFamily_one.{u, max (u + 1) v} R E IX IY
    (dgGluingHomTargetNormalizationHomInput R C D E p q X Y)
  have he := congrArg (fun g : complexPinchedSpace.{u, max (u + 1) v}
      (dgGluingHomComplex R C D M X Y) ⟶
      DGNerve.pinchedHom R E (q.obj X.right) (q.obj Y.right) =>
    dgGluingDGCompositionTriangleFamily R E
      (SSet.const (pinchedClosedVertex R E (dgHomGluingTargetMap R C D E p q X))) g)
    (dgGluingHomTargetNormalizationHomInput_source R C D E p q X Y)
  have hn := dgGluingDGCompositionTriangleFamily_precomp R E
    (SSet.const (pinchedClosedVertex R E (dgHomGluingTargetMap R C D E p q X)))
    (dgGluingHomTargetRightCoefficientInput R C D E p q X Y)
    (complexPinchedMap.{u, max (u + 1) v} (dgGluingRightHomMap R C D M X Y))
  simp only [SSet.comp_const] at hn
  exact h.trans (he.trans hn.symm)

lemma dgGluingHomTargetExitCapTriangle_zero_standard :
    (Δ[2] ◁ (ι₀ : complexPinchedSpace.{u, max (u + 1) v}
      (dgGluingHomComplex R C D M X Y) ⟶ _)) ≫
      dgGluingExitUnitCapTriangleFamily.{u, max (u + 1) v} R E IX IY
        (dgGluingHomTargetNormalizationHomInput R C D E p q X Y) =
    (Δ[2] ◁ complexPinchedMap.{u, max (u + 1) v} (dgGluingLeftHomMap R C D M X Y)) ≫
      dgGluingHomTargetLeftCompositionTriangle R C D E p q X Y := by
  have h := dgGluingExitUnitCapTriangleFamily_zero.{u, max (u + 1) v} R E IX IY
    (dgGluingHomTargetNormalizationHomInput R C D E p q X Y)
  have he := congrArg (fun g : complexPinchedSpace.{u, max (u + 1) v}
      (dgGluingHomComplex R C D M X Y) ⟶
      DGNerve.pinchedHom R E (p.obj X.left) (p.obj Y.left) =>
    dgGluingDGCompositionTriangleFamily R E g
      (SSet.const (pinchedClosedVertex R E (dgHomGluingTargetMap R C D E p q Y))))
    (dgGluingHomTargetNormalizationHomInput_replacement R C D E p q X Y)
  have hn := dgGluingDGCompositionTriangleFamily_precomp R E
    (dgGluingHomTargetLeftCoefficientInput R C D E p q X Y)
    (SSet.const (pinchedClosedVertex R E (dgHomGluingTargetMap R C D E p q Y)))
    (complexPinchedMap.{u, max (u + 1) v} (dgGluingLeftHomMap R C D M X Y))
  simp only [SSet.comp_const] at hn
  exact h.trans (he.trans hn.symm)

end SerrePositivity.InfinityCategories
