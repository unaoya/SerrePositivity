module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ValueSupportWeak

/-!
# 元の単体集合族の依存和と値の singleton

概要：同じ添字を保持する各次数の依存和と、元の各項との singleton 同型を作る。
方針：添字の等式で元の要素を移送する。
規約：空の添字も許し、元の各単体作用素を保持する。
使われ方：非指定生成列で添字付けた因子の直積の和。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.IndexedSum
open _root_.CategoryTheory

variable {I : Type u} (A : I → SSet.{u})

def space : SSet.{u} where
  obj n := Σ i, (A i).obj n
  map θ := ↾fun x => ⟨x.1, (A x.1).map θ x.2⟩
  map_id n := by
    apply ConcreteCategory.hom_ext
    intro x
    exact congrArg (Sigma.mk x.1) ((A x.1).map_id_apply n x.2)
  map_comp θ φ := by
    apply ConcreteCategory.hom_ext
    intro x
    exact congrArg (Sigma.mk x.1) ((A x.1).map_comp_apply θ φ x.2)

def label : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.IndexedSum.space A ⟶ (Functor.const SimplexCategoryᵒᵖ).obj I where
  app _ := ↾fun x => x.1
  naturality _ _ _ := rfl

def inclusion (i : I) : A i ⟶ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.IndexedSum.space A where
  app _ := ↾fun x => ⟨i, x⟩
  naturality _ _ _ := rfl

def singletonIso (i : I) : (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ValueSupport.subcomplex (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.IndexedSum.label A) {i}).toFunctor ≅ A i :=
  NatIso.ofComponents (fun _ => Equiv.toIso
    { toFun x := x.property ▸ x.val.2
      invFun x := ⟨⟨i, x⟩, rfl⟩
      left_inv x := by
        obtain ⟨⟨j, x⟩, hj⟩ := x
        change j = i at hj
        cases hj
        rfl
      right_inv _ := rfl }) (fun θ => by
    apply ConcreteCategory.hom_ext
    intro x
    obtain ⟨⟨j, x⟩, hj⟩ := x
    change j = i at hj
    cases hj
    rfl)

variable {A} {B : I → SSet.{u}} (f : ∀ i, A i ⟶ B i)

def map : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.IndexedSum.space A ⟶ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.IndexedSum.space B where
  app n := ↾fun x => ⟨x.1, (f x.1).app n x.2⟩
  naturality n m θ := by
    apply ConcreteCategory.hom_ext
    intro x
    exact congrArg (Sigma.mk x.1) (congrArg (fun k => k x.2) ((f x.1).naturality θ))

lemma map_label : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.IndexedSum.map f ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.IndexedSum.label B = _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.IndexedSum.label A := rfl

lemma singletonIso_naturality (i : I) :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ValueSupport.restriction (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.IndexedSum.label A) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.IndexedSum.label B) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.IndexedSum.map f) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.IndexedSum.map_label f) {i} ≫
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.IndexedSum.singletonIso B i).hom = (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.IndexedSum.singletonIso A i).hom ≫ f i := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro x
  obtain ⟨⟨j, x⟩, hj⟩ := x
  change j = i at hj
  cases hj
  rfl

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.IndexedSum
