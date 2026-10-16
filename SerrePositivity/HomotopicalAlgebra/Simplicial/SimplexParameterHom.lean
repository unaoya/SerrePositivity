module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionHom
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PushoutProduct
public import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex

/-! # Whole simplex-parameter families as an actual mapping simplicial set

The native closed Hom is isomorphic to this explicit model in every
degree. No model structure or choice of resolutions is involved.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalClosed
open scoped SSet.modelCategoryQuillen

namespace SerrePositivity.SimplicialModel.SimplexParameterHom
variable (K P : SSet.{v})

abbrev family : SimplexCategory ⥤ SSet.{v} := SSet.stdSimplex ⋙ tensorLeft K

abbrev obj : SSet.{v} := (HomotopyFunctionComplex.cosimplicialHom (family K)).obj P

def nativeEquiv (n : SimplexCategory) :
    (K ⊗ SSet.stdSimplex.obj n ⟶ P) ≃ ((ihom K).obj P).obj (Opposite.op n) :=
  ((ihom.adjunction K).homEquiv _ _).trans SSet.yonedaEquiv

lemma nativeEquiv_operator {n m : SimplexCategory} (θ : m ⟶ n)
    (h : K ⊗ SSet.stdSimplex.obj n ⟶ P) :
    nativeEquiv K P m (K ◁ SSet.stdSimplex.map θ ≫ h) =
      ((ihom K).obj P).map θ.op (nativeEquiv K P n h) := by
  change SSet.yonedaEquiv (curry (K ◁ SSet.stdSimplex.map θ ≫ h)) = _
  rw [curry_natural_left]
  exact (SSet.yonedaEquiv_naturality θ (curry h)).symm

def nativeIso : obj K P ≅ (ihom K).obj P :=
  NatIso.ofComponents (fun n => (nativeEquiv K P n.unop).toIso) (by
    intro n m θ
    apply ConcreteCategory.hom_ext
    intro h
    exact nativeEquiv_operator K P θ.unop h)

def map {K' P' : SSet.{v}} (i : K' ⟶ K) (q : P ⟶ P') : obj K P ⟶ obj K' P' where
  app n := ↾fun h => (i ▷ SSet.stdSimplex.obj n.unop) ≫ h ≫ q
  naturality {_ _} θ := by
    apply ConcreteCategory.hom_ext
    intro h
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro x
    rfl

def composeFamily {K P Q : SSet.{v}} {n : SimplexCategory}
    (f : K ⊗ SSet.stdSimplex.obj n ⟶ P) (g : P ⊗ SSet.stdSimplex.obj n ⟶ Q) :
    K ⊗ SSet.stdSimplex.obj n ⟶ Q :=
  lift f (snd K (SSet.stdSimplex.obj n)) ≫ g

def identityFamily (n : SimplexCategory) : K ⊗ SSet.stdSimplex.obj n ⟶ K :=
  fst K (SSet.stdSimplex.obj n)

lemma identity_comp {n : SimplexCategory} (f : K ⊗ SSet.stdSimplex.obj n ⟶ P) :
    composeFamily (identityFamily K n) f = f := by
  ext m x
  rfl

lemma comp_identity {n : SimplexCategory} (f : K ⊗ SSet.stdSimplex.obj n ⟶ P) :
    composeFamily f (identityFamily P n) = f := by
  ext m x
  rfl

lemma compose_assoc {K P Q R : SSet.{v}} {n : SimplexCategory}
    (f : K ⊗ SSet.stdSimplex.obj n ⟶ P) (g : P ⊗ SSet.stdSimplex.obj n ⟶ Q)
    (h : Q ⊗ SSet.stdSimplex.obj n ⟶ R) :
    composeFamily (composeFamily f g) h = composeFamily f (composeFamily g h) := by
  ext m x
  rfl

def bifunctor : SSet.{v}ᵒᵖ × SSet.{v} ⥤ SSet.{v} where
  obj b := obj b.1.unop b.2
  map {b _} f := map b.1.unop b.2 f.1.unop f.2
  map_id b := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro h
    apply NatTrans.ext
    funext m
    apply ConcreteCategory.hom_ext
    intro x
    rfl
  map_comp f g := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro h
    apply NatTrans.ext
    funext m
    apply ConcreteCategory.hom_ext
    intro x
    rfl

def composition (Q : SSet.{v}) : obj K P ⊗ obj P Q ⟶ obj K Q where
  app _ := ↾fun x => composeFamily x.1 x.2
  naturality {_ _} _ := by
    apply ConcreteCategory.hom_ext
    intro x
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro y
    rfl

lemma native_kan (hP : SSet.modelCategoryQuillen.J.rlp (terminal.from P)) :
    SSet.modelCategoryQuillen.J.rlp (terminal.from ((ihom K).obj P)) := by
  have : HomotopicalAlgebra.Fibration (terminal.from P) :=
    (SSet.modelCategoryQuillen.fibration_iff _).mpr hP
  have : SSet.KanComplex P := (HomotopicalAlgebra.isFibrant_iff P).mpr inferInstance
  exact (SSet.modelCategoryQuillen.fibration_iff _).mp inferInstance

lemma kan (hP : SSet.modelCategoryQuillen.J.rlp (terminal.from P)) :
    SSet.modelCategoryQuillen.J.rlp (terminal.from (obj K P)) := by
  have he : (nativeIso K P).hom ≫ terminal.from ((ihom K).obj P) =
      terminal.from (obj K P) := terminal.hom_ext _ _
  rw [← he]
  exact SSet.modelCategoryQuillen.J.rlp.comp_mem _ _
    (SSet.modelCategoryQuillen.J.rlp.of_isIso _) (native_kan K P hP)

end SerrePositivity.SimplicialModel.SimplexParameterHom
