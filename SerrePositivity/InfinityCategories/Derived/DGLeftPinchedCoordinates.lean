module
public import SerrePositivity.InfinityCategories.Derived.DGLeftPinchedChainMap
public import SerrePositivity.InfinityCategories.F1.CoherentLeftHomEnrichedNaturality
/-!
概要：左 pinched Hom の反対模型同型と coslice fiber 同型の、実全単体の座標を計算する。
方針：端点輸送を消去し、同じ反対 dg 単体と同じ join 単体を回収する。
規約：全次数の実等式。使われ方：閉始点前合成と実 fiber 射の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerveOppositeData SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] (x y : D)
/-- 同じ左 Hom の反対模型同型は、元の実全単体の符号付き反転である。 -/
lemma dgLeftPinchedOppositeIso_hom_val {n : ℕ}
    (s : (pinchedHomLeft (X := dgNerve R D) (Simplex.vertex x) (Simplex.vertex y)) _⦋n⦌) :
    (SSet.opObjEquiv ((dgLeftPinchedOppositeIso R D x y).hom.app _ s)).val =
      opSimplex (pinchedLeftSimplexVal n s) := by
  change ((eqToHom (congrArg₂ (fun a b ↦ InfinityCategories.pinchedHom
    (X := dgNerve R Dᵒᵖ) a b)
    (dgNerveOppositeIso_hom_vertex R D y) (dgNerveOppositeIso_hom_vertex R D x))).app _
      ((pinchedHomMap (dgNerveOppositeIso R D).hom
        (SSet.opObjEquiv.symm (Simplex.vertex y))
        (SSet.opObjEquiv.symm (Simplex.vertex x))).app _ (SSet.opObjEquiv s))).val = _
  rw [pinchedHom_eqToHom_app_val (dgNerveOppositeIso_hom_vertex R D y)
    (dgNerveOppositeIso_hom_vertex R D x)]
  rfl
/-- 左 Hom の同じ coslice fiber 同型は、元の同じ全単体を保つ。 -/
lemma dgLeftPinchedCosliceFiberIso_simplex {X : SSet.{w}}
    (a b : X _⦋0⦌) {n : ℕ} (s : (pinchedHomLeft a b) _⦋n⦌) :
    cosliceFiberSimplex n ((pinchedLeftCosliceFiberIso a b).hom.app _ s) =
      pinchedLeftSimplexVal n s := by
  change cosliceFiberSimplex n ((cosliceFiberSimplexEquiv a b n).symm
    ((pinchedLeftSimplexEquiv a b n) s)) = _
  rw [cosliceFiberSimplex_equiv_symm]
  rfl
end SerrePositivity.InfinityCategories
