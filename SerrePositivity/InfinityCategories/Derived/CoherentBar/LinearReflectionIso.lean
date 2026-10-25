module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.LinearReflectionNaturality
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerve.PinchedHom DGNerveOppositeIndex SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] (x y : C)

def dgCoherentBarPinchedReflectionSimplex {n : ℕ}
    (s : (DGNerve.pinchedHom R C x y) _⦋n⦌) :
    (DGNerve.pinchedHom R C x y) _⦋n⦌ :=
  (dgCoherentBarLinearReflectionSimplex (toLinearSimplex s)).toPinched

lemma dgCoherentBarPinchedReflectionSimplex_linear {n : ℕ}
    (s : (DGNerve.pinchedHom R C x y) _⦋n⦌) :
    toLinearSimplex (dgCoherentBarPinchedReflectionSimplex R C x y s) =
      dgCoherentBarLinearReflectionSimplex (toLinearSimplex s) :=
  LinearSimplex.toLinearSimplex_toPinched _

lemma dgCoherentBarPinchedReflectionSimplex_involution {n : ℕ}
    (s : (DGNerve.pinchedHom R C x y) _⦋n⦌) :
    dgCoherentBarPinchedReflectionSimplex R C x y
      (dgCoherentBarPinchedReflectionSimplex R C x y s) = s := by
  apply (linearEquiv x y n).injective
  change toLinearSimplex _ = toLinearSimplex s
  rw [dgCoherentBarPinchedReflectionSimplex_linear, dgCoherentBarPinchedReflectionSimplex_linear,
    dgCoherentBarLinearReflectionSimplex_involution]

def dgCoherentBarPinchedReflectionDegreeEquiv (n : ℕ) :
    ((DGNerve.pinchedHom R C x y).op) _⦋n⦌ ≃ (DGNerve.pinchedHom R C x y) _⦋n⦌ where
  toFun s := dgCoherentBarPinchedReflectionSimplex R C x y (SSet.opObjEquiv s)
  invFun s := SSet.opObjEquiv.symm (dgCoherentBarPinchedReflectionSimplex R C x y s)
  left_inv s := by
    apply SSet.opObjEquiv.injective
    exact dgCoherentBarPinchedReflectionSimplex_involution R C x y (SSet.opObjEquiv s)
  right_inv s := dgCoherentBarPinchedReflectionSimplex_involution R C x y s

def dgCoherentBarPinchedReflectionIso : (DGNerve.pinchedHom R C x y).op ≅
    DGNerve.pinchedHom R C x y :=
  NatIso.ofComponents
    (fun n => Equiv.toIso (dgCoherentBarPinchedReflectionDegreeEquiv R C x y n.unop.len)) (by
      intro n m α
      apply ConcreteCategory.hom_ext
      intro s
      apply (linearEquiv x y m.unop.len).injective
      change toLinearSimplex
        (dgCoherentBarPinchedReflectionSimplex R C x y
          (SSet.opObjEquiv (((DGNerve.pinchedHom R C x y).op).map α s))) =
        toLinearSimplex ((dgCoherentBarPinchedReflectionSimplex R C x y
          (SSet.opObjEquiv s)).pullback α.unop)
      rw [dgCoherentBarPinchedReflectionSimplex_linear, toLinearSimplex_pullback,
        dgCoherentBarPinchedReflectionSimplex_linear]
      change dgCoherentBarLinearReflectionSimplex
        (toLinearSimplex ((SSet.opObjEquiv s).pullback (SimplexCategory.rev.map α.unop))) = _
      rw [toLinearSimplex_pullback]
      have hRev : (SimplexCategory.rev.map α.unop).toOrderHom =
          reverseOrderHom α.unop.toOrderHom := by
        ext i
        rfl
      rw [hRev]
      exact dgCoherentBarLinearReflectionSimplex_pullback α.unop.toOrderHom
        (toLinearSimplex (SSet.opObjEquiv s)))

end SerrePositivity.InfinityCategories
