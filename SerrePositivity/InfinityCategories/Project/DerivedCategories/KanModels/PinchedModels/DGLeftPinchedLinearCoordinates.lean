module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.PinchedModels.DGLeftPinchedCoordinates
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.PinchedModels.PinchedChainMapComposition
/-!
概要：左 pinched Hom の全単体を、同じ dg 反対 Hom の線形削除方程式で座標化する。
方針：同じ反対 nerve 同型と既存の右線形同値を合成し、全係数と鎖写像の作用を保つ。
規約：全次数の実比較。使われ方：coslice の実 fiber 射と Hom 鎖写像の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] {x y : D}
/-- 左 Hom の全単体と、同じ反対 Hom の線形単体との同値。 -/
def dgLeftPinchedLinearEquiv (x y : D) (n : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)) _⦋n⦌ ≃
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex R (Opposite.op y) (Opposite.op x) n :=
  (CategoryTheory.Iso.toEquiv ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLeftPinchedOppositeIso R D x y).app
    (Opposite.op ⦋n⦌))).trans
      (SSet.opObjEquiv.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.linearEquiv (A := R) (Opposite.op y) (Opposite.op x) n))
/-- 同じ線形座標の各係数は、元の実反対単体の対応する係数。 -/
lemma dgLeftPinchedLinearEquiv_component_heq {n : ℕ}
    (t : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)) _⦋n⦌)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    HEq ((dgLeftPinchedLinearEquiv R D x y n t).val.component J k hJ hk)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.opSimplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedLeftSimplexVal n t)).hom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast J)
        (J.min' hJ).castSucc (Fin.last (n + 1)) k
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.two_withLast hJ) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.min_withLast hJ _) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.max_withLast J _)
        (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.card_withLast]; omega)) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearData_component_heq
    (SSet.opObjEquiv ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLeftPinchedOppositeIso R D x y).hom.app _ t)) J k hJ hk
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLeftPinchedOppositeIso_hom_val] at h
  exact h
/-- 元の左 Hom 全単体の始対象は指定始点。 -/
lemma dgLeftPinchedSimplex_obj_zero {n : ℕ}
    (t : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)) _⦋n⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedLeftSimplexVal n t).obj 0 = x := by
  exact congrArg (fun a : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R D 0 ↦ a.obj 0) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedLeftSimplexVal_source n t)
/-- 元の左 Hom 全単体の正番号の対象は指定終点。 -/
lemma dgLeftPinchedSimplex_obj_ne_zero {n : ℕ}
    (t : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)) _⦋n⦌)
    (i : Fin (n + 2)) (hi : i ≠ 0) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedLeftSimplexVal n t).obj i = y := by
  obtain ⟨j, rfl⟩ := Fin.eq_succ_of_ne_zero hi
  exact congrArg (fun a : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R D n ↦ a.obj j) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedLeftSimplexVal_target n t)
variable (E : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] {x' y' : E}
lemma dgLeftPinchedChainMap_linear
    (φ : _root_.SerrePositivity.DifferentialGraded.homObject R D x y ⟶ _root_.SerrePositivity.DifferentialGraded.homObject R E x' y') {n : ℕ}
    (t : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)) _⦋n⦌) :
    dgLeftPinchedLinearEquiv R E x' y' n ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLeftPinchedChainMap R D E φ).app _ t) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearSimplexMap (D := Dᵒᵖ) (E := Eᵒᵖ) φ (dgLeftPinchedLinearEquiv R D x y n t) := by
  have H : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLeftPinchedChainMap R D E φ ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLeftPinchedOppositeIso R E x' y').hom =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLeftPinchedOppositeIso R D x y).hom ≫
        SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (A := R) (D := Dᵒᵖ) (E := Eᵒᵖ)
          (x := Opposite.op y) (y := Opposite.op x)
          (x' := Opposite.op y') (y' := Opposite.op x') φ) := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLeftPinchedChainMap, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app H (Opposite.op ⦋n⦌)) t
  have hh := congrArg (fun z ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex (SSet.opObjEquiv z)) h
  change _ = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMapSimplex (D := Dᵒᵖ) (E := Eᵒᵖ) φ
    (SSet.opObjEquiv ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLeftPinchedOppositeIso R D x y).hom.app _ t))) at hh
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMapSimplex_linear] at hh
  exact hh
end SerrePositivity.InfinityCategories.Project.DerivedCategories
