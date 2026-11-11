module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanMonoRelativeHomotopy
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering

/-!
概要：Kan 値の二つの全円柱の比較を、指定した始面と部分円柱から厳密に延長する。
方針：端点と部分円柱の pushout-product 上で比較を貼り、同じ単射の相対延長を使う。
規約：始面・部分円柱・比較の両端を同時に保持する。
使われ方：元の第一行亜群化円柱の商像と商 core 円柱との全比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.LocalizingInvariants

/-- 始面と部分円柱上で一致する二つの指定比較を、同じ全円柱比較へ延長する。 -/
lemma exists_kanCylinderComparison {S K Z : SSet.{u}} (j : S ⟶ K) [Mono j] [KanComplex Z]
    (F G : K ⊗ (Δ[1] : SSet.{u}) ⟶ Z)
    (H₀ : SSet.Homotopy ((K ◁ stdSimplex.δ (1 : Fin 2)) ≫ F)
      ((K ◁ stdSimplex.δ (1 : Fin 2)) ≫ G))
    (Hₛ : SSet.Homotopy ((j ▷ (Δ[1] : SSet.{u})) ≫ F)
      ((j ▷ (Δ[1] : SSet.{u})) ≫ G))
    (hc : ((j ▷ (Δ[0] : SSet.{u})) ▷ (Δ[1] : SSet.{u})) ≫ H₀.h =
      ((S ◁ stdSimplex.δ (1 : Fin 2)) ▷ (Δ[1] : SSet.{u})) ≫ Hₛ.h) :
    ∃ H : SSet.Homotopy F G,
      ((K ◁ stdSimplex.δ (1 : Fin 2)) ▷ (Δ[1] : SSet.{u})) ≫ H.h = H₀.h ∧
      ((j ▷ (Δ[1] : SSet.{u})) ▷ (Δ[1] : SSet.{u})) ≫ H.h = Hₛ.h := by
  let pp := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{u}) j
    (stdSimplex.δ (1 : Fin 2))
  have ha : anodyneExtensions pp.ι :=
    anodyneExtensions_pushoutObjObjι pp (AnodyneHomotopy.delta_anodyne 1 0 (by decide))
  have hL : pp.inl ≫ pp.ι = K ◁ stdSimplex.δ (1 : Fin 2) := pp.inl_ι
  have hR : pp.inr ≫ pp.ι = j ▷ (Δ[1] : SSet.{u}) := pp.inr_ι
  have : Mono (Arrow.mk j).hom := inferInstanceAs (Mono j)
  have : Mono (Arrow.mk (stdSimplex.δ (1 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1])).hom :=
    inferInstanceAs (Mono (stdSimplex.δ (1 : Fin 2)))
  have : Mono pp.ι :=
    CategoryTheory.MonoidalCategory.Arrow.PushoutProduct.instMonoHomObjArrowFunctorPushoutProduct
      (X := Arrow.mk j) (Y := Arrow.mk (stdSimplex.δ (1 : Fin 2)))
  let tsq := pp.isPushout.map (tensorRight (Δ[1] : SSet.{u}))
  let w := tsq.desc H₀.h Hₛ.h hc
  have h₀ : (pp.inl ▷ (Δ[1] : SSet.{u})) ≫ w = H₀.h := tsq.inl_desc _ _ _
  have hₛ : (pp.inr ▷ (Δ[1] : SSet.{u})) ≫ w = Hₛ.h := tsq.inr_desc _ _ _
  let W : SSet.Homotopy (pp.ι ≫ F) (pp.ι ≫ G) :=
    { h := w
      h₀ := by
        change SSet.ι₀ ≫ w = pp.ι ≫ F
        apply pp.isPushout.hom_ext
        · rw [← Category.assoc, ← SSet.ι₀_comp, Category.assoc, h₀, H₀.h₀,
            ← Category.assoc, hL]
        · rw [← Category.assoc, ← SSet.ι₀_comp, Category.assoc, hₛ, Hₛ.h₀,
            ← Category.assoc, hR]
      h₁ := by
        change SSet.ι₁ ≫ w = pp.ι ≫ G
        apply pp.isPushout.hom_ext
        · rw [← Category.assoc, ← SSet.ι₁_comp, Category.assoc, h₀, H₀.h₁,
            ← Category.assoc, hL]
        · rw [← Category.assoc, ← SSet.ι₁_comp, Category.assoc, hₛ, Hₛ.h₁,
            ← Category.assoc, hR]
      rel := by
        apply SSet.hom_ext
        intro n
        apply ConcreteCategory.hom_ext
        intro v
        exact False.elim v.1.property }
  have hZ : modelCategoryQuillen.J.rlp (terminal.from Z) :=
    (modelCategoryQuillen.fibration_iff _).mp inferInstance
  obtain ⟨H, hH⟩ := SerrePositivity.SimplicialModel.KanMonoRelativeHomotopy.exists_extension
    pp.ι (anodyneExtensions.Q_inverts _ ha) hZ F G W
  refine ⟨H, ?_, ?_⟩
  · calc
      _ = ((pp.inl ≫ pp.ι) ▷ (Δ[1] : SSet.{u})) ≫ H.h :=
        congrArg (fun x => (x ▷ (Δ[1] : SSet.{u})) ≫ H.h) hL.symm
      _ = H₀.h := by rw [comp_whiskerRight, Category.assoc, hH]; exact h₀
  · calc
      _ = ((pp.inr ≫ pp.ι) ▷ (Δ[1] : SSet.{u})) ≫ H.h :=
        congrArg (fun x => (x ▷ (Δ[1] : SSet.{u})) ≫ H.h) hR.symm
      _ = Hₛ.h := by rw [comp_whiskerRight, Category.assoc, hH]; exact hₛ

end SerrePositivity.KST.LocalizingInvariants
