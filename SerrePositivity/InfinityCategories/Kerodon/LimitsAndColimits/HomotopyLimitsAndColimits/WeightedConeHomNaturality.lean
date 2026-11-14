module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedConeSimplex
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedCoherentCoefficientNaturality
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.ClosedVertexWhiskering

/-!
概要：元のweighted cone単体の全豊穣Homの厳密自然性。
方針：頂点の単位・尾部の通常自然性・混合係数の双方向自然性・空Homに分ける。
規約：IS-W2 D01の既存構成の自然性・貼り合わせ則。元の全高次単体を保つ。
使われ方：Kerodon 7.5.4、同じ指定錐のStrictCoherentFamilyへの接続。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open CategoryTheory SimplicialThickening SSet
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open scoped Simplicial
variable {C : Type v} [Category.{u} C] [SimplicialCategory C]

/-- 元のweighted coneの尾部のHomは同じ通常図式射に自然。 -/
theorem weightedConeTailHom_naturality {n : ℕ} {F G : Fin (n + 1) ⥤ C}
    (η : F ⟶ G) (i j : Fin (n + 1)) :
    weightedConeTailHom F i j ≫ eHomWhiskerLeft SSet (F.obj i) (η.app j) =
      weightedConeTailHom G i j ≫ eHomWhiskerRight SSet (η.app i) (G.obj j) := by
  apply SSet.hom_ext
  rintro ⟨⟨r⟩⟩
  apply ConcreteCategory.hom_ext
  intro P
  have hij : i ≤ j := Fin.succ_le_succ_iff.mp
    (show i.succ ≤ j.succ from
      Path.le (J := ULift.{u} (Fin (n + 2))) (P.obj 0))
  have h : eHomEquiv SSet (F.map (homOfLE hij)) ≫
      eHomWhiskerLeft SSet (F.obj i) (η.app j) =
    eHomEquiv SSet (G.map (homOfLE hij)) ≫
      eHomWhiskerRight SSet (η.app i) (G.obj j) := by
    rw [closedVertex_whiskerLeft, closedVertex_whiskerRight, η.naturality]
  have hc := ConcreteCategory.congr_hom (NatTrans.congr_app h (Opposite.op ⦋r⦌)) PUnit.unit
  simp only [NatTrans.comp_app, types_comp_apply] at hc
  erw [unitHom_app_constant (eHomEquiv SSet (F.map (homOfLE hij))) r,
    unitHom_app_constant (eHomEquiv SSet (G.map (homOfLE hij))) r] at hc
  exact hc

variable {I : Type u} [SmallCategory I] {F G : I ⥤ C}

/-- 元の図式射による同じ豊穣Hom図式の後合成。 -/
def weightedConeHomTargetMap (η : F ⟶ G) (x : C) :
    simplicialHomDiagram F x ⟶ simplicialHomDiagram G x :=
  Functor.whiskerRight η ((SimplicialCategory.sHomFunctor C).obj (Opposite.op x))

/-- 元の頂点射による同じ豊穣Hom図式の前合成。 -/
def weightedConeHomSourceMap {x y : C} (f : x ⟶ y) (G : I ⥤ C) :
    simplicialHomDiagram G y ⟶ simplicialHomDiagram G x :=
  Functor.whiskerLeft G ((SimplicialCategory.sHomFunctor C).map f.op)

/-- 元のweighted coneの各頂点での同じ通常射。 -/
def weightedConeVertexMap {n : ℕ} (η : F ⟶ G) {x y : C} (f : x ⟶ y)
    (σ : ComposableArrows I n) (i : Fin (n + 2)) :
    weightedConeObj x (σ ⋙ F) i ⟶ weightedConeObj y (σ ⋙ G) i :=
  Fin.cases f (fun j => η.app (σ.obj j)) i

/-- 元のweighted coneの全Homは、同じ頂点射・図式射の作用に可換する。 -/
theorem weightedConeHom_naturality {n : ℕ} {σ : ComposableArrows I n}
    (η : F ⟶ G) {x y : C} (f : x ⟶ y)
    (τ : simplexPrefixWeight n ⟶ σ ⋙ simplicialHomDiagram F x ⋙ SSet.opFunctor)
    (τ' : simplexPrefixWeight n ⟶ σ ⋙ simplicialHomDiagram G y ⋙ SSet.opFunctor)
    (h : τ ≫ Functor.whiskerLeft σ
        (Functor.whiskerRight (weightedConeHomTargetMap η x) SSet.opFunctor) =
      τ' ≫ Functor.whiskerLeft σ
        (Functor.whiskerRight (weightedConeHomSourceMap f G) SSet.opFunctor))
    (i j : Fin (n + 2)) :
    weightedConeHom F x τ i j ≫ eHomWhiskerLeft SSet
        (weightedConeObj x (σ ⋙ F) i) (weightedConeVertexMap η f σ j) =
      weightedConeHom G y τ' i j ≫ eHomWhiskerRight SSet
        (weightedConeVertexMap η f σ i) (weightedConeObj y (σ ⋙ G) j) := by
  induction i using Fin.cases <;> induction j using Fin.cases
  case zero.zero =>
    change (_ ≫ eId SSet x) ≫ eHomWhiskerLeft SSet x f =
      (_ ≫ eId SSet y) ≫ eHomWhiskerRight SSet f y
    rw [Category.assoc, Category.assoc, enrichedUnit_whiskering]
  case zero.succ j =>
    exact weightedCoherentCoefficient_dinaturality
      (weightedConeHomTargetMap η x) (weightedConeHomSourceMap f G) τ τ' h j
  case succ.zero i =>
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro P
    have hp := Path.le (J := ULift.{u} (Fin (n + 2))) (P.obj 0)
    change i.val + 1 ≤ (0 : ℕ) at hp
    omega
  case succ.succ i j =>
    exact weightedConeTailHom_naturality (Functor.whiskerLeft σ η) i j

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
