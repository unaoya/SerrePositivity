module
public import SerrePositivity.InfinityCategories.Derived.DGNerveOppositeIso
public import SerrePositivity.InfinityCategories.Derived.PinchedChainMapQuasiIso
public import SerrePositivity.InfinityCategories.F1.PinchedHomIso
public import SerrePositivity.InfinityCategories.F1B.KanQCatEquivalenceOpposite
public import SerrePositivity.InfinityCategories.F1.CoslicePinchedLeft
/-!
概要：左 pinched Hom を dg 反対模型の右 pinched Hom へ移し、全 Hom 鎖写像を作用させる。
方針：同じ符号付き反対 nerve 同型と端点の厳密等式を使い、右模型の準同型不変性を移す。
規約：対象の小ささも前三角性も不要。使われ方：実 coslice fiber の全次数比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D]
/-- 左 pinched Hom と dg 反対模型の同じ右 Hom の反転との実同型。 -/
def dgLeftPinchedOppositeIso (x y : D) :
    pinchedHomLeft (X := dgNerve R D) (Simplex.vertex x) (Simplex.vertex y) ≅
      (DGNerve.pinchedHom R Dᵒᵖ (Opposite.op y) (Opposite.op x)).op :=
  SSet.opFunctor.mapIso
    (pinchedHomIsoOfIso (dgNerveOppositeIso R D)
      (SSet.opObjEquiv.symm (Simplex.vertex y))
      (SSet.opObjEquiv.symm (Simplex.vertex x)) ≪≫
      eqToIso (congrArg₂ (fun a b ↦ InfinityCategories.pinchedHom
        (X := dgNerve R Dᵒᵖ) a b)
        (dgNerveOppositeIso_hom_vertex R D y) (dgNerveOppositeIso_hom_vertex R D x)))
variable (E : Type v) [DGCategory R E] {x y : D} {x' y' : E}
/-- 同じ全 Hom 鎖写像による、左 pinched Hom の全単体上の作用。 -/
def dgLeftPinchedChainMap (φ : homObject R D x y ⟶ homObject R E x' y') :
    pinchedHomLeft (X := dgNerve R D) (Simplex.vertex x) (Simplex.vertex y) ⟶
    pinchedHomLeft (X := dgNerve R E) (Simplex.vertex x') (Simplex.vertex y') :=
  (dgLeftPinchedOppositeIso R D x y).hom ≫
    SSet.opFunctor.map (pinchedHomChainMap (A := R) (D := Dᵒᵖ) (E := Eᵒᵖ)
      (x := Opposite.op y) (y := Opposite.op x)
      (x' := Opposite.op y') (y' := Opposite.op x') φ) ≫
    (dgLeftPinchedOppositeIso R E x' y').inv
lemma dgLeftPinchedChainMap_isQCatEquivalence
    (φ : homObject R D x y ⟶ homObject R E x' y') [QuasiIso φ] :
    IsQCatEquivalence (dgLeftPinchedChainMap R D E φ) := by
  have h := (pinchedHomChainMap_quasiIso_equivalence (A := R) (D := Dᵒᵖ) (E := Eᵒᵖ)
    (x := Opposite.op y) (y := Opposite.op x)
    (x' := Opposite.op y') (y' := Opposite.op x') φ).isQCatEquivalence
  exact (qCatEquivalenceOfIso (dgLeftPinchedOppositeIso R D x y)).isQCatEquivalence.comp
    ((F1B.kanIsQCatEquivalence_op h).comp
      (qCatEquivalenceOfIso (dgLeftPinchedOppositeIso R E x' y').symm).isQCatEquivalence)
end SerrePositivity.InfinityCategories
