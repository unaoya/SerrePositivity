module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.LinearReflectionNaturality
/-!
概要：反転した右 pinched Hom と元の右 pinched Hom の実単体集合同型を作る。
方針：全次数の線形反転同値を、全添字写像との可換性で束ねる。
規約：同じ Hom 複体の反転だけを使い、逆射をホモトピーで選ばない。
使われ方：dg 反対模型を経る左 Hom を、固定終点の右 Hom と比較する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] (x y : C)

def dgCoherentBarPinchedReflectionSimplex {n : ℕ}
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R C x y) _⦋n⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R C x y) _⦋n⦌ :=
  (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarLinearReflectionSimplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex s)).toPinched

lemma dgCoherentBarPinchedReflectionSimplex_linear {n : ℕ}
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R C x y) _⦋n⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex (dgCoherentBarPinchedReflectionSimplex R C x y s) =
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarLinearReflectionSimplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex s) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearSimplex_toPinched _

lemma dgCoherentBarPinchedReflectionSimplex_involution {n : ℕ}
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R C x y) _⦋n⦌) :
    dgCoherentBarPinchedReflectionSimplex R C x y
      (dgCoherentBarPinchedReflectionSimplex R C x y s) = s := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.linearEquiv x y n).injective
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex _ = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex s
  rw [dgCoherentBarPinchedReflectionSimplex_linear, dgCoherentBarPinchedReflectionSimplex_linear,
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarLinearReflectionSimplex_involution]

def dgCoherentBarPinchedReflectionDegreeEquiv (n : ℕ) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R C x y).op) _⦋n⦌ ≃ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R C x y) _⦋n⦌ where
  toFun s := dgCoherentBarPinchedReflectionSimplex R C x y (SSet.opObjEquiv s)
  invFun s := SSet.opObjEquiv.symm (dgCoherentBarPinchedReflectionSimplex R C x y s)
  left_inv s := by
    apply SSet.opObjEquiv.injective
    exact dgCoherentBarPinchedReflectionSimplex_involution R C x y (SSet.opObjEquiv s)
  right_inv s := dgCoherentBarPinchedReflectionSimplex_involution R C x y s

def dgCoherentBarPinchedReflectionIso : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R C x y).op ≅
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R C x y :=
  NatIso.ofComponents
    (fun n => Equiv.toIso (dgCoherentBarPinchedReflectionDegreeEquiv R C x y n.unop.len)) (by
      intro n m α
      apply ConcreteCategory.hom_ext
      intro s
      apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.linearEquiv x y m.unop.len).injective
      change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex
        (dgCoherentBarPinchedReflectionSimplex R C x y
          (SSet.opObjEquiv (((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R C x y).op).map α s))) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex ((dgCoherentBarPinchedReflectionSimplex R C x y
          (SSet.opObjEquiv s)).pullback α.unop)
      rw [dgCoherentBarPinchedReflectionSimplex_linear, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearSimplex_pullback,
        dgCoherentBarPinchedReflectionSimplex_linear]
      change _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarLinearReflectionSimplex
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex ((SSet.opObjEquiv s).pullback (SimplexCategory.rev.map α.unop))) = _
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearSimplex_pullback]
      have hRev : (SimplexCategory.rev.map α.unop).toOrderHom =
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.reverseOrderHom α.unop.toOrderHom := by
        ext i
        rfl
      rw [hRev]
      exact _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarLinearReflectionSimplex_pullback α.unop.toOrderHom
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex (SSet.opObjEquiv s)))

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
