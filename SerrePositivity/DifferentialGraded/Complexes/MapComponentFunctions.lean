module
public import SerrePositivity.DifferentialGraded.Complexes.MapEvaluation

/-! # 指定された成分関数で複体の射を再表示する -/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex
variable {A : Type u} [CommRing A] {X Y : Complex A}

/-- 成分関数とその既存chain mapへの一致から、成分を明示したchain mapを構成する。 -/
def chainMapOfComponentFunctions (f : X ⟶ Y) (F : ∀ n, X.X n → Y.X n)
    (h : ∀ n x, F n x = f.f n x) : X ⟶ Y where
  f n := ModuleCat.ofHom {
    toFun := F n
    map_add' := fun x y => by rw [h, h, h]; exact map_add (f.f n).hom x y
    map_smul' := fun a x => by rw [h, h]; exact map_smul (f.f n).hom a x }
  comm' i j hij := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change Y.d i j (F i x) = F j (X.d i j x)
    rw [h, h]
    exact ConcreteCategory.congr_hom (f.comm i j) x

@[simp]
lemma chainMapOfComponentFunctions_apply (f : X ⟶ Y) (F : ∀ n, X.X n → Y.X n)
    (h : ∀ n x, F n x = f.f n x) (n : ℤ) (x : X.X n) :
    (chainMapOfComponentFunctions f F h).f n x = F n x := rfl

lemma chainMapOfComponentFunctions_eq (f : X ⟶ Y) (F : ∀ n, X.X n → Y.X n)
    (h : ∀ n x, F n x = f.f n x) : chainMapOfComponentFunctions f F h = f := by
  apply chain_ext_apply
  exact h

end SerrePositivity.DifferentialGraded
