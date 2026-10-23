module
public import SerrePositivity.InfinityCategories.Derived.DGLeftPinchedLinearCoordinates
public import SerrePositivity.InfinityCategories.Derived.DGWalkingHomPinched
public import SerrePositivity.InfinityCategories.Derived.DGNerveOppositeFunctor
public import SerrePositivity.InfinityCategories.F1.Coherent.LeftHomEnrichedNaturality
/-!
概要：実 dg 関手の左 Hom への作用を、同じ全 Hom 鎖写像の作用へ同定する。
方針：全単体の関手像と反対 dg 模型の自然性を照合し、同じ二端点へ正規化する。
規約：全高次・全係数の実等式。使われ方：Hom 関手族の実 fiber 比較の合成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerveOppositeData SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] {D E : Type v} [DGCategory R D] [DGCategory R E]
  (F : DGFunctor R D E) (x y : D)
/-- 同じ dg 関手の実左 Hom 写像を、標準の実両端点へ正規化したもの。 -/
def dgLeftPinchedFunctorMap :
    pinchedHomLeft (X := dgNerve R D) (Simplex.vertex x) (Simplex.vertex y) ⟶
    pinchedHomLeft (X := dgNerve R E) (Simplex.vertex (F.obj x)) (Simplex.vertex (F.obj y)) :=
  pinchedHomLeftMap (dgNerve.map F) (Simplex.vertex x) (Simplex.vertex y) ≫
    eqToHom (congrArg₂ (fun a b ↦ pinchedHomLeft (X := dgNerve R E) a b)
      (dgFunctorNerve_vertex F x) (dgFunctorNerve_vertex F y))
/-- 同じ実左 Hom 関手写像は、元の全単体の同じ dg 関手像を保つ。 -/
lemma dgLeftPinchedFunctorMap_val {n : ℕ}
    (t : (pinchedHomLeft (X := dgNerve R D) (Simplex.vertex x) (Simplex.vertex y)) _⦋n⦌) :
    pinchedLeftSimplexVal n ((dgLeftPinchedFunctorMap R F x y).app _ t) =
      (pinchedLeftSimplexVal n t).map F := by
  change pinchedLeftSimplexVal n ((eqToHom (congrArg₂
    (fun a b ↦ pinchedHomLeft (X := dgNerve R E) a b)
    (dgFunctorNerve_vertex F x) (dgFunctorNerve_vertex F y))).app _ _) = _
  rw [pinchedHomLeft_eqToHom_app_val (dgFunctorNerve_vertex F x) (dgFunctorNerve_vertex F y)]
  exact pinchedHomLeftMap_app_val (dgNerve.map F) t
/-- 同じ Hom 鎖写像の左 Hom 作用も、元の全単体の同じ dg 関手像を保つ。 -/
lemma dgLeftPinchedChainMap_functor_val {n : ℕ}
    (t : (pinchedHomLeft (X := dgNerve R D) (Simplex.vertex x) (Simplex.vertex y)) _⦋n⦌) :
    pinchedLeftSimplexVal n ((dgLeftPinchedChainMap R D E (F.map x y)).app _ t) =
      (pinchedLeftSimplexVal n t).map F := by
  apply (simplexEquiv R E (n + 1)).injective
  have H : dgLeftPinchedChainMap R D E (F.map x y) ≫
      (dgLeftPinchedOppositeIso R E (F.obj x) (F.obj y)).hom =
      (dgLeftPinchedOppositeIso R D x y).hom ≫
        SSet.opFunctor.map (pinchedHomChainMap (A := R) (D := Dᵒᵖ) (E := Eᵒᵖ)
          (x := Opposite.op y) (y := Opposite.op x)
          (x' := Opposite.op (F.obj y)) (y' := Opposite.op (F.obj x)) (F.map x y)) := by
    rw [dgLeftPinchedChainMap, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have h := congrArg (fun (g :
      pinchedHomLeft (X := dgNerve R D) (Simplex.vertex x) (Simplex.vertex y) ⟶
      (DGNerve.pinchedHom R Eᵒᵖ (Opposite.op (F.obj y)) (Opposite.op (F.obj x))).op) ↦
      (SSet.opObjEquiv (g.app (Opposite.op ⦋n⦌) t)).val) H
  change (SSet.opObjEquiv ((dgLeftPinchedOppositeIso R E (F.obj x) (F.obj y)).hom.app _
      ((dgLeftPinchedChainMap R D E (F.map x y)).app _ t))).val =
    ((pinchedHomChainMap (A := R) (D := Dᵒᵖ) (E := Eᵒᵖ)
      (x := Opposite.op y) (y := Opposite.op x)
      (x' := Opposite.op (F.obj y)) (y' := Opposite.op (F.obj x)) (F.map x y)).app _
      (SSet.opObjEquiv ((dgLeftPinchedOppositeIso R D x y).hom.app _ t))).val at h
  rw [dgLeftPinchedOppositeIso_hom_val] at h
  have hf := dgFunctorPinchedChainMap_val R F.op
    (x := Opposite.op y) (y := Opposite.op x)
    (SSet.opObjEquiv ((dgLeftPinchedOppositeIso R D x y).hom.app _ t))
  have hh := h.trans hf
  rw [dgLeftPinchedOppositeIso_hom_val] at hh
  change opSimplex _ = opSimplex _
  rw [hh]
  apply Simplex.ext
  exact (dgOppositeData_map (pinchedLeftSimplexVal n t).toSimplexData F).symm
/-- 実 dg 関手の左 Hom 写像は、同じ全 Hom 鎖写像の作用に等しい。 -/
lemma dgLeftPinchedFunctorMap_eq_chainMap :
    dgLeftPinchedFunctorMap R F x y = dgLeftPinchedChainMap R D E (F.map x y) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro t
  apply pinchedLeftSimplexVal_injective n
  rw [dgLeftPinchedFunctorMap_val, dgLeftPinchedChainMap_functor_val]
/-- 同じ全 Hom 鎖写像の左 Hom 作用は、実合成を厳密に保つ。 -/
lemma dgLeftPinchedChainMap_comp {T : Type v} [DGCategory R T]
    {a b : D} {a' b' : E} {a'' b'' : T}
    (φ : homObject R D a b ⟶ homObject R E a' b')
    (ψ : homObject R E a' b' ⟶ homObject R T a'' b'') :
    dgLeftPinchedChainMap R D T (φ ≫ ψ) =
      dgLeftPinchedChainMap R D E φ ≫ dgLeftPinchedChainMap R E T ψ := by
  simp only [dgLeftPinchedChainMap, Category.assoc, Iso.inv_hom_id_assoc]
  erw [pinchedHomChainMap_comp (A := R) (D := Dᵒᵖ) (E := Eᵒᵖ) (T := Tᵒᵖ) φ ψ,
    Functor.map_comp]
  simp only [Category.assoc]
end SerrePositivity.InfinityCategories
