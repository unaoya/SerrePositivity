module

public import SerrePositivity.AlgebraicGeometry.FinitePresentationModelColimit
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import SerrePositivity.AlgebraicGeometry.SchemeVCoverComposition
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.CategoryTheory.Limits.Preserves.Opposites

/-!
概要：任意の代数を有限表示の模型の Spec の実際の逆極限として表す。
方針：環の filtered colimit を op と右随伴 Spec の極限保存で移す。
規約：各段の基底への射には元の R-代数構造を使う。忠実平坦性は仮定しない。
使われ方：Rydh 3.10 の整全射の有限表示段による近似。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
universe u
variable (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]

/-- 任意の代数の有限表示模型の Spec の逆系。 -/
def finitePresentationModelSpecDiagram : (FinitePresentationModelIndex R B)ᵒᵖ ⥤ Scheme.{u} :=
  (finitePresentationModelSmallDiagram R B).op ⋙ Scheme.Spec

/-- 元の Spec B と、模型の実際の構造射からなる cone。 -/
def finitePresentationModelSpecCone : Cone (finitePresentationModelSpecDiagram R B) :=
  Scheme.Spec.mapCone (finitePresentationModelSmallCocone R B).op

/-- 任意の代数の実際の Spec は、有限表示模型の Spec の逆極限。 -/
def finitePresentationModelSpecConeIsLimit :
    IsLimit (finitePresentationModelSpecCone R B) :=
  isLimitOfPreserves Scheme.Spec (IsColimit.op (finitePresentationModelSmallCoconeIsColimit R B))

/-- 模型の元の R-代数構造を使う基底への射。 -/
def finitePresentationModelSpecBaseMap (i : FinitePresentationModelIndex R B) :
    (finitePresentationModelSpecDiagram R B).obj (.op i) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom
    (algebraMap R ((equivSmallModel (FinitePresentationModelCategory R B)).inverse.obj i).obj.left.obj))

/-- 模型の基底への射は局所有限表示。 -/
instance finitePresentationModelSpecBaseMap_locallyOfFinitePresentation (i : FinitePresentationModelIndex R B) :
    LocallyOfFinitePresentation (finitePresentationModelSpecBaseMap R B i) := by
  apply (LocallyOfFinitePresentation.SpecMap_iff _).mpr
  change (algebraMap R ((equivSmallModel (FinitePresentationModelCategory R B)).inverse.obj i).obj.left.obj).FinitePresentation
  exact RingHom.finitePresentation_algebraMap.mpr
    ((equivSmallModel (FinitePresentationModelCategory R B)).inverse.obj i).property

/-- 極限 cone の射影は、模型の実際の B への準同型の Spec。 -/
theorem finitePresentationModelSpecCone_projection (i : FinitePresentationModelIndex R B) :
    (finitePresentationModelSpecCone R B).π.app (.op i) =
      Spec.map ((finitePresentationModelSmallCocone R B).ι.app i) := rfl

/-- 射影と基底への射の合成は、元の R→B の Spec。 -/
theorem finitePresentationModelSpecCone_projection_comp (i : FinitePresentationModelIndex R B) :
    (finitePresentationModelSpecCone R B).π.app (.op i) ≫ finitePresentationModelSpecBaseMap R B i =
      Spec.map (CommRingCat.ofHom (algebraMap R B)) := by
  change Spec.map (CommRingCat.ofHom
    ((equivSmallModel (FinitePresentationModelCategory R B)).inverse.obj i).obj.hom.hom.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap R
      ((equivSmallModel (FinitePresentationModelCategory R B)).inverse.obj i).obj.left.obj)) = _
  rw [← Spec.map_comp]
  congr 1
  ext r
  exact ((equivSmallModel (FinitePresentationModelCategory R B)).inverse.obj i).obj.hom.hom.commutes r

/-- 元の Spec が基底上全射なら、各有限表示段も基底上全射。 -/
theorem finitePresentationModelSpecBaseMap_surjective
    [hSurj : Surjective (Spec.map (CommRingCat.ofHom (algebraMap R B)))]
    (i : FinitePresentationModelIndex R B) : Surjective (finitePresentationModelSpecBaseMap R B i) := by
  letI : Surjective ((finitePresentationModelSpecCone R B).π.app (.op i) ≫
      finitePresentationModelSpecBaseMap R B i) := by
    rw [finitePresentationModelSpecCone_projection_comp]
    exact hSurj
  exact Surjective.of_comp (f := (finitePresentationModelSpecCone R B).π.app (.op i))
    (g := finitePresentationModelSpecBaseMap R B i)

/-- 元の affine v 被覆から、同じ基底上の各有限表示模型の v 判定を得る。 -/
theorem finitePresentationModelSpecBaseMap_vCover
    (hf : IsSchemeVCover (Spec.map (CommRingCat.ofHom (algebraMap R B))))
    (i : FinitePresentationModelIndex R B) :
    IsSchemeVCover (finitePresentationModelSpecBaseMap R B i) := by
  apply IsSchemeVCover.of_comp
    (f := (finitePresentationModelSpecCone R B).π.app (.op i))
  rw [finitePresentationModelSpecCone_projection_comp]
  exact hf

/-- B04 の基底への構造射は、実際の模型の全ての遷移と可換。 -/
theorem finitePresentationModelSpecBaseMap_naturality
    {j k : (FinitePresentationModelIndex R B)ᵒᵖ} (f : j ⟶ k) :
    (finitePresentationModelSpecDiagram R B).map f ≫ finitePresentationModelSpecBaseMap R B k.unop =
      finitePresentationModelSpecBaseMap R B j.unop := by
  change Spec.map ((finitePresentationModelSmallDiagram R B).map f.unop) ≫
    finitePresentationModelSpecBaseMap R B k.unop = finitePresentationModelSpecBaseMap R B j.unop
  dsimp only [finitePresentationModelSpecBaseMap]
  rw [← Spec.map_comp]
  congr 1
  ext z
  exact (((equivSmallModel (FinitePresentationModelCategory R B)).inverse.map f.unop).hom.left.hom.hom).commutes z

/-- B04 の実際の図式を元の Spec R の上の図式にする自然変換。 -/
def finitePresentationModelSpecBaseNatTrans : finitePresentationModelSpecDiagram R B ⟶
    (Functor.const (FinitePresentationModelIndex R B)ᵒᵖ).obj (Spec (CommRingCat.of R)) where
  app j := finitePresentationModelSpecBaseMap R B j.unop
  naturality j k f := by simpa using finitePresentationModelSpecBaseMap_naturality R B f

/-- B04 の cone は、元の Spec B→Spec R の上で可換。 -/
theorem finitePresentationModelSpecCone_base (j : (FinitePresentationModelIndex R B)ᵒᵖ) :
    (finitePresentationModelSpecCone R B).π.app j ≫ (finitePresentationModelSpecBaseNatTrans R B).app j =
      Spec.map (CommRingCat.ofHom (algebraMap R B)) :=
  finitePresentationModelSpecCone_projection_comp R B j.unop


end SerrePositivity.AlgebraicGeometry
