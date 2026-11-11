module
public import SerrePositivity.KST.SConstruction.DiagonalReduction
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorHomotopy

/-! # 全単体で自然な実円柱の、同じパラメータを保つ対角評価と両端の回収 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Fibration

/-- 指定した元の区間族の始点の式を、同じ実評価円柱の始点へ移す。 -/
theorem uncurryIntervalFamily_zero {X Y : SSet.{u}}
    (H : (Δ[1] : SSet.{u}) ⟶ (ihom X).obj Y) (f : X ⟶ Y)
    (hf : stdSimplex.δ (1 : Fin 2) ≫ H = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f)) :
    SSet.ι₀ ≫ uncurry H = f := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_uncurry_zero (SSet.yonedaEquiv H)
  rw [Equiv.symm_apply_apply] at h
  have he := congrArg SSet.yonedaEquiv hf
  rw [stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply] at he
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_injective (h.trans he)

/-- 指定した元の区間族の終点の式を、同じ実評価円柱の終点へ移す。 -/
theorem uncurryIntervalFamily_one {X Y : SSet.{u}}
    (H : (Δ[1] : SSet.{u}) ⟶ (ihom X).obj Y) (f : X ⟶ Y)
    (hf : stdSimplex.δ (0 : Fin 2) ≫ H = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f)) :
    SSet.ι₁ ≫ uncurry H = f := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_uncurry_one (SSet.yonedaEquiv H)
  rw [Equiv.symm_apply_apply] at h
  have he := congrArg SSet.yonedaEquiv hf
  rw [stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply] at he
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_injective (h.trans he)

/-- 元の全段のパラメータ付き実射を、同じ各次数の評価のまま対角へ送る。 -/
def simplicialCylinderDiagonal (F G : SimplexCategoryᵒᵖ ⥤ SSet.{u}) (P : SSet.{u})
    (H : F ⋙ tensorRight P ⟶ G) :
    simplicialDiagonalFunctor.obj F ⊗ P ⟶ simplicialDiagonalFunctor.obj G where
  app n := (H.app n).app n
  naturality {n m} θ := by
    apply ConcreteCategory.hom_ext
    rintro ⟨x, p⟩
    have h₁ := congrArg (fun f => f.app n (x, p)) (H.naturality θ)
    have h₂ := CategoryTheory.types_congr_hom ((H.app m).naturality θ)
      ((F.map θ).app n x, p)
    exact h₂.trans (congrArg (fun z => (G.obj m).map θ z) h₁)

/-- 元の全単体的射の後合成は、同じ実対角円柱の後合成を厳密に回収する。 -/
theorem simplicialCylinderDiagonal_postcomp {F G G' : SimplexCategoryᵒᵖ ⥤ SSet.{u}}
    {P : SSet.{u}} (H : F ⋙ tensorRight P ⟶ G) (g : G ⟶ G') :
    simplicialCylinderDiagonal F G' P (H ≫ g) =
      simplicialCylinderDiagonal F G P H ≫ simplicialDiagonalFunctor.map g := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  rfl

/-- 元の全単体的射の前合成も、同じ実対角円柱の前合成を厳密に回収する。 -/
theorem simplicialCylinderDiagonal_precomp {F' F G : SimplexCategoryᵒᵖ ⥤ SSet.{u}}
    {P : SSet.{u}} (f : F' ⟶ F) (H : F ⋙ tensorRight P ⟶ G) :
    simplicialCylinderDiagonal F' G P
      (CategoryTheory.Functor.whiskerRight f (tensorRight P) ≫ H) =
      (simplicialDiagonalFunctor.map f ▷ P) ≫ simplicialCylinderDiagonal F G P H := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  rfl

/-- 元の全段の始点の等式は、同じ対角円柱の始点の等式を与える。 -/
theorem simplicialCylinderDiagonal_zero {F G : SimplexCategoryᵒᵖ ⥤ SSet.{u}}
    (H : F ⋙ tensorRight (Δ[1] : SSet.{u}) ⟶ G) (f : F ⟶ G)
    (hf : ∀ n, SSet.ι₀ ≫ H.app n = f.app n) :
    SSet.ι₀ ≫ simplicialCylinderDiagonal F G Δ[1] H = simplicialDiagonalFunctor.map f := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  exact congrArg (fun t => t.app n x) (hf n)

/-- 元の全段の終点の等式は、同じ対角円柱の終点の等式を与える。 -/
theorem simplicialCylinderDiagonal_one {F G : SimplexCategoryᵒᵖ ⥤ SSet.{u}}
    (H : F ⋙ tensorRight (Δ[1] : SSet.{u}) ⟶ G) (f : F ⟶ G)
    (hf : ∀ n, SSet.ι₁ ≫ H.app n = f.app n) :
    SSet.ι₁ ≫ simplicialCylinderDiagonal F G Δ[1] H = simplicialDiagonalFunctor.map f := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  exact congrArg (fun t => t.app n x) (hf n)

end SerrePositivity.KST.Fibration
