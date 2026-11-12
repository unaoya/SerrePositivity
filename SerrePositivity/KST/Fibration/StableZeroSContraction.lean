module
public import SerrePositivity.KST.Fibration.StableZeroEndContraction
public import SerrePositivity.KST.SConstruction.SExactEnrichedFunctor

/-! # 一つの元の零自己関手の収縮による、全 S_n に自然な同じ全円柱 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

/-- 同じ元の収縮辺を、元の全自然変換の S_n 作用へ写した全族。 -/
def stableZeroSContractionFamily (A : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) (n : ℕ) :
    (Δ[1] : SSet.{u}) ⟶ (ihom (sConstruction n A.obj)).obj (sConstruction n A.obj) :=
  stableZeroEndContractionFamily A ≫ sExactFamilyMap n A A

/-- 同じ元の S_n 族の評価による、全パラメータの実円柱。 -/
def stableZeroSContractionAction (A : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) (n : ℕ) :
    sConstruction n A.obj ⊗ (Δ[1] : SSet.{u}) ⟶ sConstruction n A.obj :=
  uncurry (stableZeroSContractionFamily A n)

/-- 同じ一つの元の収縮族の S_n 像は、全ての面・退化で厳密に自然。 -/
theorem stableZeroSContractionFamily_reindex (A : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) {m n : ℕ}
    (θ : Fin (m + 1) →o Fin (n + 1)) :
    stableZeroSContractionFamily A n ≫ (ihom (sConstruction n A.obj)).map (sMap A.obj θ) =
      stableZeroSContractionFamily A m ≫ (pre (sMap A.obj θ)).app (sConstruction m A.obj) :=
  (Category.assoc _ _ _).trans
    ((congrArg (stableZeroEndContractionFamily A ≫ ·)
      (sExactFamilyMap_restriction A A θ)).trans (Category.assoc _ _ _).symm)

/-- 元の収縮円柱は、全ての面・退化と全時刻で厳密に可換。 -/
theorem stableZeroSContractionAction_reindex (A : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) {m n : ℕ}
    (θ : Fin (m + 1) →o Fin (n + 1)) :
    (sMap A.obj θ ▷ (Δ[1] : SSet.{u})) ≫ stableZeroSContractionAction A m =
      stableZeroSContractionAction A n ≫ sMap A.obj θ := by
  have h := congrArg (uncurry (C := SSet.{u})) (stableZeroSContractionFamily_reindex A θ)
  rw [uncurry_natural_right, uncurry_pre_app] at h
  exact h.symm

/-- 全時刻で面・退化に自然な元の収縮円柱を、同じ単体的図式の射として保持。 -/
def stableZeroSContractionNatTrans (A : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) :
    simplicialSConstruction A.obj ⋙ tensorRight (Δ[1] : SSet.{u}) ⟶
      simplicialSConstruction A.obj where
  app n := stableZeroSContractionAction A n.unop.len
  naturality {_ _} θ := stableZeroSContractionAction_reindex A θ.unop.toOrderHom

/-- 元の全 S_n 族の始点は、同じ元の零自己関手による S_n 完全射。 -/
theorem stableZeroSContractionFamily_zero (A : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) (n : ℕ) :
    stdSimplex.δ (1 : Fin 2) ≫ stableZeroSContractionFamily A n =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (sExactMap n (stableZeroEndMap A)).hom) := by
  rw [stableZeroSContractionFamily, ← Category.assoc, stableZeroEndContractionFamily_zero,
    SSet.yonedaEquiv_symm_comp, sExactFamilyMap_vertex]
  rfl

/-- 元の全 S_n 族の終点は、同じ元の恒等関手。 -/
theorem stableZeroSContractionFamily_one (A : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) (n : ℕ) :
    stdSimplex.δ (0 : Fin 2) ≫ stableZeroSContractionFamily A n =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (𝟙 (sConstruction n A.obj))) := by
  rw [stableZeroSContractionFamily, ← Category.assoc, stableZeroEndContractionFamily_one,
    SSet.yonedaEquiv_symm_comp, sExactFamilyMap_vertex]
  have hi : (sExactMap n (show A ⟶ A from 𝟙 A)).hom = 𝟙 (sConstruction n A.obj) :=
    sPostcomp_id n A.obj
  exact congrArg (fun f => SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f)) hi

end SerrePositivity.KST.Fibration
