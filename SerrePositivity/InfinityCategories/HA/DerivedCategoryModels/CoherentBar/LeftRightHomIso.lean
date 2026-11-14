module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.LinearReflectionIso
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.NativeColimitPointHomCriterion
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.PinchedModels.DGLeftPinchedLinearCoordinates
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
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial

def dgCoherentBarPinchedUnopIso (R : Type u) [CommRing R]
    (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] (x y : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R Cᵒᵖ (Opposite.op y) (Opposite.op x) ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R C x y := by
  let φ : _root_.SerrePositivity.DifferentialGraded.homObject R Cᵒᵖ (Opposite.op y) (Opposite.op x) ⟶ homObject R C x y := 𝟙 _
  have : IsIso φ := inferInstance
  have : IsIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (A := R) (D := Cᵒᵖ) (E := C)
      (x := Opposite.op y) (y := Opposite.op x) (x' := x) (y' := y) φ) :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap_isIso φ
  exact asIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap φ)

def dgCoherentBarLeftRightHomIso (R : Type u) [CommRing R]
    (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] (x y : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y) ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R C x y :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLeftPinchedOppositeIso R C x y ≪≫
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarPinchedReflectionIso R Cᵒᵖ (Opposite.op y) (Opposite.op x) ≪≫
      dgCoherentBarPinchedUnopIso R C x y

variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))
  (hMC : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarMaurerCartan R D F)
  (y : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D)) _⦋0⦌)

def dgCoherentBarNativeLeftRightHomIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedNativeCocone R D F hMC).vertex y ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R (RightModule R D) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModule R D F hMC)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv R (RightModule R D) y) :=
  eqToIso (congrArg₂ (fun a b => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D)) a b)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedNativeCocone_vertex R D F hMC)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv R (RightModule R D)).symm_apply_apply y).symm) ≪≫
      dgCoherentBarLeftRightHomIso R (_root_.SerrePositivity.DifferentialGraded.RightModule R D)
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModule R D F hMC) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv R (RightModule R D) y)

lemma dgCoherentBarNativeLeftRightHomIso_homotopyEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (dgCoherentBarNativeLeftRightHomIso R D F hMC y).hom :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (dgCoherentBarNativeLeftRightHomIso R D F hMC y)).isQCatEquivalence
    |>.isSimplicialHomotopyEquivalence

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
