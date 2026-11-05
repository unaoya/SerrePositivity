module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.LinearReflectionIso
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.NativeColimitPointHomCriterion
public import SerrePositivity.InfinityCategories.Derived.DGLeftPinchedLinearCoordinates
/-!
概要：dg nerve の左右 pinched Hom を、明示的な線形反転による厳密同型で結ぶ。
方針：dg 反対模型への既存の同型、線形反転、同じ Hom 複体の恒等鎖写像を合成する。
規約：標準族との一致は後続の課題として保持し、native 余極限性を先取りしない。
使われ方：固定終点経路での標準 Hom の族の合成の照合先。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped _root_.Simplicial

def dgCoherentBarPinchedUnopIso (R : Type u) [CommRing R]
    (C : Type v) [DGCategory R C] (x y : C) :
    DGNerve.pinchedHom R Cᵒᵖ (Opposite.op y) (Opposite.op x) ≅ DGNerve.pinchedHom R C x y := by
  let φ : homObject R Cᵒᵖ (Opposite.op y) (Opposite.op x) ⟶ homObject R C x y := 𝟙 _
  have : IsIso φ := inferInstance
  have : IsIso (pinchedHomChainMap (A := R) (D := Cᵒᵖ) (E := C)
      (x := Opposite.op y) (y := Opposite.op x) (x' := x) (y' := y) φ) :=
    pinchedHomChainMap_isIso φ
  exact asIso (pinchedHomChainMap φ)

def dgCoherentBarLeftRightHomIso (R : Type u) [CommRing R]
    (C : Type v) [DGCategory R C] (x y : C) :
    pinchedHomLeft (X := dgNerve R C) (Simplex.vertex x) (Simplex.vertex y) ≅
      DGNerve.pinchedHom R C x y :=
  dgLeftPinchedOppositeIso R C x y ≪≫
    dgCoherentBarPinchedReflectionIso R Cᵒᵖ (Opposite.op y) (Opposite.op x) ≪≫
      dgCoherentBarPinchedUnopIso R C x y

variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))
  (hMC : dgCoherentBarMaurerCartan R D F)
  (y : (dgNerve R (RightModule R D)) _⦋0⦌)

def dgCoherentBarNativeLeftRightHomIso :
    pinchedHomLeft (dgCoherentBarNormalizedNativeCocone R D F hMC).vertex y ≅
      DGNerve.pinchedHom R (RightModule R D) (dgCoherentBarNormalizedModule R D F hMC)
        (dgNerve.vertexEquiv R (RightModule R D) y) :=
  eqToIso (congrArg₂ (fun a b => pinchedHomLeft (X := dgNerve R (RightModule R D)) a b)
    (dgCoherentBarNormalizedNativeCocone_vertex R D F hMC)
    ((dgNerve.vertexEquiv R (RightModule R D)).symm_apply_apply y).symm) ≪≫
      dgCoherentBarLeftRightHomIso R (RightModule R D)
        (dgCoherentBarNormalizedModule R D F hMC) (dgNerve.vertexEquiv R (RightModule R D) y)

lemma dgCoherentBarNativeLeftRightHomIso_homotopyEquivalence :
    IsSimplicialHomotopyEquivalence (dgCoherentBarNativeLeftRightHomIso R D F hMC y).hom :=
  (qCatEquivalenceOfIso (dgCoherentBarNativeLeftRightHomIso R D F hMC y)).isQCatEquivalence
    |>.isSimplicialHomotopyEquivalence

end SerrePositivity.InfinityCategories
