module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.PinchedModels.DGLeftPinchedLinearCoordinates
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.PinchedModels.DGWalkingHomPinched
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.FunctorComparisons.DGNerveOppositeFunctor
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LeftHomEnrichedNaturality
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] {D E : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E]
  (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R D E) (x y : D)
/-- 同じ dg 関手の実左 Hom 写像を、標準の実両端点へ正規化したもの。 -/
def dgLeftPinchedFunctorMap :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (F.obj x)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (F.obj y)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LeftHomEnrichedNaturality.pinchedHomLeftMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y) ≫
    eqToHom (congrArg₂ (fun a b ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E) a b)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex F x) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex F y))
/-- 同じ実左 Hom 関手写像は、元の全単体の同じ dg 関手像を保つ。 -/
lemma dgLeftPinchedFunctorMap_val {n : ℕ}
    (t : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)) _⦋n⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedLeftSimplexVal n ((dgLeftPinchedFunctorMap R F x y).app _ t) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedLeftSimplexVal n t).map F := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedLeftSimplexVal n ((eqToHom (congrArg₂
    (fun a b ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E) a b)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex F x) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex F y))).app _ _) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LeftHomEnrichedNaturality.pinchedHomLeft_eqToHom_app_val (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex F x) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex F y)]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LeftHomEnrichedNaturality.pinchedHomLeftMap_app_val (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F) t
/-- 同じ Hom 鎖写像の左 Hom 作用も、元の全単体の同じ dg 関手像を保つ。 -/
lemma dgLeftPinchedChainMap_functor_val {n : ℕ}
    (t : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)) _⦋n⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedLeftSimplexVal n ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLeftPinchedChainMap R D E (F.map x y)).app _ t) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedLeftSimplexVal n t).map F := by
  apply (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplexEquiv R E (n + 1)).injective
  have H : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLeftPinchedChainMap R D E (F.map x y) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLeftPinchedOppositeIso R E (F.obj x) (F.obj y)).hom =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLeftPinchedOppositeIso R D x y).hom ≫
        SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (A := R) (D := Dᵒᵖ) (E := Eᵒᵖ)
          (x := Opposite.op y) (y := Opposite.op x)
          (x' := Opposite.op (F.obj y)) (y' := Opposite.op (F.obj x)) (F.map x y)) := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLeftPinchedChainMap, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have h := congrArg (fun (g :
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y) ⟶
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R Eᵒᵖ (Opposite.op (F.obj y)) (Opposite.op (F.obj x))).op) ↦
      (SSet.opObjEquiv (g.app (Opposite.op ⦋n⦌) t)).val) H
  change (SSet.opObjEquiv ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLeftPinchedOppositeIso R E (F.obj x) (F.obj y)).hom.app _
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLeftPinchedChainMap R D E (F.map x y)).app _ t))).val =
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (A := R) (D := Dᵒᵖ) (E := Eᵒᵖ)
      (x := Opposite.op y) (y := Opposite.op x)
      (x' := Opposite.op (F.obj y)) (y' := Opposite.op (F.obj x)) (F.map x y)).app _
      (SSet.opObjEquiv ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLeftPinchedOppositeIso R D x y).hom.app _ t))).val at h
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLeftPinchedOppositeIso_hom_val] at h
  have hf := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorPinchedChainMap_val R F.op
    (x := Opposite.op y) (y := Opposite.op x)
    (SSet.opObjEquiv ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLeftPinchedOppositeIso R D x y).hom.app _ t))
  have hh := h.trans hf
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLeftPinchedOppositeIso_hom_val] at hh
  change _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.opSimplex _ = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.opSimplex _
  rw [hh]
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOppositeData_map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedLeftSimplexVal n t).toSimplexData F).symm
/-- 実 dg 関手の左 Hom 写像は、同じ全 Hom 鎖写像の作用に等しい。 -/
lemma dgLeftPinchedFunctorMap_eq_chainMap :
    dgLeftPinchedFunctorMap R F x y = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLeftPinchedChainMap R D E (F.map x y) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro t
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedLeftSimplexVal_injective n
  rw [dgLeftPinchedFunctorMap_val, dgLeftPinchedChainMap_functor_val]
/-- 同じ全 Hom 鎖写像の左 Hom 作用は、実合成を厳密に保つ。 -/
lemma dgLeftPinchedChainMap_comp {T : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory R T]
    {a b : D} {a' b' : E} {a'' b'' : T}
    (φ : _root_.SerrePositivity.DifferentialGraded.homObject R D a b ⟶ _root_.SerrePositivity.DifferentialGraded.homObject R E a' b')
    (ψ : _root_.SerrePositivity.DifferentialGraded.homObject R E a' b' ⟶ _root_.SerrePositivity.DifferentialGraded.homObject R T a'' b'') :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLeftPinchedChainMap R D T (φ ≫ ψ) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLeftPinchedChainMap R D E φ ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLeftPinchedChainMap R E T ψ := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLeftPinchedChainMap, Category.assoc, Iso.inv_hom_id_assoc]
  erw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap_comp (A := R) (D := Dᵒᵖ) (E := Eᵒᵖ) (T := Tᵒᵖ) φ ψ,
    Functor.map_comp]
  simp only [Category.assoc]
end SerrePositivity.InfinityCategories.Project.DerivedCategories
