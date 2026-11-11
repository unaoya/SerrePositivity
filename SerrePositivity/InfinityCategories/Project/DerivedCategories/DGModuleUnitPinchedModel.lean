module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGSemifreeDerivedHomAugmentationInfinity
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PinchedComplexModelComparison
public import SerrePositivity.DifferentialGraded.Module.Basic
/-!
概要：全 dg R 加群の実 nerve で、R の代表加群からの Hom を同じ評価複体へ同定する。
方針：全 Hom の Yoneda 同型と単位 Hom 同型を、同じ実 pinched 鎖写像へ送る。
規約：対象だけを共通宇宙へ上げる。使われ方：基礎空間の全 ∞ 関手の値の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v)
/-- 共通対象宇宙で読む R の代表加群。 -/
def dgHomModuleUnit (_D : Type v) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{u + 1, max (u + 1) v} (RightModule R PUnit.{1}) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp R (RightModule R PUnit.{1})).obj (representable R PUnit.unit)
/-- 同じ R の代表加群を、全加群の実 nerve の頂点として読む。 -/
abbrev dgHomModuleUnitVertex : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomModuleNerve R D) _⦋0⦌ :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (dgHomModuleUnit R D)
/-- R の代表加群からの実 pinched Hom は、同じ加群の評価複体の pinched 模型と同型。 -/
def dgHomModuleUnderlyingPinchedIso (M : _root_.SerrePositivity.DifferentialGraded.RightModule R PUnit.{1}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{u + 1, max (u + 1) v} (RightModule R PUnit.{1}))
      (dgHomModuleUnit R D) ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp R (RightModule R PUnit.{1})).obj M) ≅
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, max (u + 1) v} (M.obj (Opposite.op PUnit.unit)) := by
  let φ := (dgYonedaIso R PUnit.unit M).hom ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso _).hom
  let f := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (A := R)
    (D := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{u + 1, max (u + 1) v} (RightModule R PUnit.{1}))
    (E := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGComplexPinchedModel.{u, max (u + 1) v} (M.obj (Opposite.op PUnit.unit)))
    (x := dgHomModuleUnit R D) (y := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp R (RightModule R PUnit.{1})).obj M)
    (x' := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSource _) (y' := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedTarget _) φ
  let : IsIso f := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap_isIso (A := R)
    (D := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{u + 1, max (u + 1) v} (RightModule R PUnit.{1}))
    (E := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGComplexPinchedModel.{u, max (u + 1) v} (M.obj (Opposite.op PUnit.unit)))
    (x := dgHomModuleUnit R D) (y := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp R (RightModule R PUnit.{1})).obj M)
    (x' := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSource _) (y' := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedTarget _) φ
  exact asIso f
end SerrePositivity.InfinityCategories.Project.DerivedCategories
