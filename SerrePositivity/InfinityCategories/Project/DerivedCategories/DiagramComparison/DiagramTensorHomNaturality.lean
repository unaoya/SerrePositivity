module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.DiagramHomFamilyEquiv
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.HomotopyIntervalNaturality
/-!
概要：図式テンソル–Hom同値の前後合成自然性。
方針：既存の転置の始域・標的自然性を同じ評価成分で束ねる。
規約：A06の前提計算3/3。既存の構成の自然性法則。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded SerrePositivity.HomologicalAlgebra
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable {A : Type (max u v)} [CommRing A] {J : Type v} [SmallCategory J]
local notation "E" => functorToComplexOfFunctors J (ModuleCat A) (ComplexShape.up ℤ)
/-- 同じ図式テンソル–Hom同値は全図式射の前後合成と可換。 -/
theorem diagramTensorLinearHomEquiv_naturality {R R' S S' : J ⥤ Complex A}
    (T : Complex A) (a : R' ⟶ R) (b : S ⟶ S') (t : R ⊗ (Functor.const J).obj T ⟶ S) :
    diagramTensorLinearHomEquiv R' S' T (((a ▷ (Functor.const J).obj T) ≫ t) ≫ b) =
      diagramTensorLinearHomEquiv R S T t ≫ intervalHomPrePost A ((E).map a) ((E).map b) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply diagramCochain_ext R' S'
  intro j
  apply Cochain.ext
  intro p q hpq
  change ((tensorHomEquiv (R'.obj j) T (S'.obj j)
    (((a.app j ▷ T) ≫ t.app j) ≫ b.app j)).f n z).v p q hpq =
      (((Cochain.ofHom ((E).map a)).comp
        (((diagramTensorLinearHomEquiv R S T t).f n z).comp
          (Cochain.ofHom ((E).map b)) (add_zero n)) (zero_add n)).v p q hpq).app j
  simp only [Cochain.zero_cochain_comp_v, Cochain.comp_zero_cochain_v,
    Cochain.ofHom_v, NatTrans.comp_app]
  change ((tensorHomEquiv (R'.obj j) T (S'.obj j)
    (((a.app j ▷ T) ≫ t.app j) ≫ b.app j)).f n z).v p q hpq =
      (a.app j).f p ≫ ((tensorHomEquiv (R.obj j) T (S.obj j) (t.app j)).f n z).v p q hpq ≫
        (b.app j).f q
  rw [tensorHomEquiv_naturality_target, tensorHomEquiv_naturality_domain]
  simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply, homPrecompose_apply,
    homPostcompose_apply, Cochain.zero_cochain_comp_v, Cochain.comp_zero_cochain_v,
    Cochain.ofHom_v, Category.assoc]
end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
