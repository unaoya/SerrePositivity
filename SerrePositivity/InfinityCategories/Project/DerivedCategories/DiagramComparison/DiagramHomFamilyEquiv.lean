module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.DiagramHomFamilyLift

/-!
概要：図式 Hom 複体への射と、自然性条件つきの点ごとの Hom 射の族を同定する。
方針：評価を逆射とし、評価の微分可換性と外延性で両合成を確認する。
規約：元の図式 Hom 複体を用い、自然性条件を保持する。
使われ方：HA 1.2.4、G10 の全単体テンソル Hom の同定。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CochainComplex HomComplex
open SerrePositivity.DifferentialGraded SerrePositivity.HomologicalAlgebra
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable {A : Type u} [CommRing A] {J : Type} [SmallCategory J]
variable (P Q : J ⥤ Complex A) (T : Complex A)
local notation "E" => functorToComplexOfFunctors J (ModuleCat A) (ComplexShape.up ℤ)

/-- 図式 Hom への射を、各点への評価で元の族へ戻す。 -/
def diagramHomFamilyOfHom (f : T ⟶ linearHomComplex A ((E).obj P) ((E).obj Q)) :
    DiagramHomFamily P Q T :=
  ⟨fun j =>
    { f := fun n => ModuleCat.ofHom
        { toFun := fun x => diagramCochainAt P Q (f.f n x) j
          map_add' := by
            intro x y
            apply Cochain.ext
            intro p q hpq
            change ((f.f n (x + y)).v p q hpq).app j = _
            rw [map_add]
            rfl
          map_smul' := by
            intro a x
            apply Cochain.ext
            intro p q hpq
            change ((f.f n (a • x)).v p q hpq).app j = _
            rw [map_smul]
            rfl }
      comm' := by
        intro n m _
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        change δ n m (diagramCochainAt P Q (f.f n x) j) =
          diagramCochainAt P Q (f.f m (T.d n m x)) j
        rw [← diagramCochainAt_delta]
        exact congrArg (fun z => diagramCochainAt P Q z j)
          (ConcreteCategory.congr_hom (f.comm n m) x) }, by
    intro i j t
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Cochain.ext
    intro p q hpq
    change ((Cochain.ofHom (P.map t)).comp
      (diagramCochainAt P Q (f.f n x) j) (zero_add n)).v p q hpq =
        ((diagramCochainAt P Q (f.f n x) i).comp
          (Cochain.ofHom (Q.map t)) (add_zero n)).v p q hpq
    simp only [Cochain.zero_cochain_comp_v, Cochain.comp_zero_cochain_v, Cochain.ofHom_v]
    exact ((f.f n x).v p q hpq).naturality t⟩

/-- 同じ図式 Hom 複体への射と自然性条件つきの族の同値。 -/
def diagramHomFamilyEquiv :
    DiagramHomFamily P Q T ≃ (T ⟶ linearHomComplex A ((E).obj P) ((E).obj Q)) where
  toFun := diagramHomFamilyLift P Q T
  invFun := diagramHomFamilyOfHom P Q T
  left_inv g := by
    apply Subtype.ext
    funext j
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl
  right_inv f := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply diagramCochain_ext P Q
    intro j
    rfl

/-- 図式テンソルの射と、元の図式 Hom 複体への射の同値。 -/
def diagramTensorLinearHomEquiv :
    (P ⊗ (Functor.const J).obj T ⟶ Q) ≃
      (T ⟶ linearHomComplex A ((E).obj P) ((E).obj Q)) :=
  (diagramTensorHomEquiv P Q T).trans (diagramHomFamilyEquiv P Q T)

/-- 同じ同値はパラメータ複体の全射による前合成と可換。 -/
theorem diagramTensorLinearHomEquiv_precomp {T' : Complex A} (g : T' ⟶ T)
    (f : P ⊗ (Functor.const J).obj T ⟶ Q) :
    diagramTensorLinearHomEquiv P Q T' ((P ◁ (Functor.const J).map g) ≫ f) =
      g ≫ diagramTensorLinearHomEquiv P Q T f := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply diagramCochain_ext P Q
  intro j
  exact ConcreteCategory.congr_hom
    (congrArg (fun h => h.f n) (diagramTensorHomEquiv_precomp P Q T g f j)) x

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
