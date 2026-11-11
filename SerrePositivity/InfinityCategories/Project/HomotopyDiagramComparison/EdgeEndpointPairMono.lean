module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoprodTensorGlue
public import Mathlib.CategoryTheory.Limits.Types.Coproducts

/-!
概要：標準区間の二端点を同時に含める射が単射であることを各次数で示す。
方針：余積の次数評価を型の直和へ移し、二端点の像が交わらないことを使う。
規約：片方の端点評価だけから同時制限の充填性を推論しない。
使われ方：根辺延長の終点評価の left fibration 性の無条件化。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

private lemma types_coprod_desc_mono {X Y Z : Type u} (f : X ⟶ Z) (g : Y ⟶ Z)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (hd : ∀ x y, f x ≠ g y) : Mono (coprod.desc f g) := by
  let e := Types.binaryCoproductIso X Y
  have he : e.inv ≫ coprod.desc f g = (↾(Sum.elim f g)) := by
    apply ConcreteCategory.hom_ext
    intro z
    cases z with
    | inl x =>
      simp only [comp_apply, TypeCat.hom_ofHom, TypeCat.Fun.coe_mk, Sum.elim_inl]
      exact ConcreteCategory.congr_hom (coprod.inl_desc f g) x
    | inr y =>
      simp only [comp_apply, TypeCat.hom_ofHom, TypeCat.Fun.coe_mk, Sum.elim_inr]
      exact ConcreteCategory.congr_hom (coprod.inr_desc f g) y
  have : Mono (e.inv ≫ coprod.desc f g) := by
    rw [he]
    apply (mono_iff_injective _).2
    intro x y h
    cases x with
    | inl x =>
      cases y with
      | inl y => exact congrArg Sum.inl (hf h)
      | inr y => exact False.elim (hd x y h)
    | inr x =>
      cases y with
      | inl y => exact False.elim (hd y x h.symm)
      | inr y => exact congrArg Sum.inr (hg h)
  have hfac : coprod.desc f g = e.hom ≫ (e.inv ≫ coprod.desc f g) := by simp
  rw [hfac]
  infer_instance

/-- 標準区間の始点と終点の結合した包含は単射である。 -/
instance edgeEndpointPair_mono :
    Mono (coprod.desc (stdSimplex.δ (1 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1])
      (stdSimplex.δ (0 : Fin 2))) := by
  rw [NatTrans.mono_iff_mono_app]
  rintro ⟨⟨n⟩⟩
  let F := (evaluation SimplexCategoryᵒᵖ (Type u)).obj (Opposite.op ⦋n⦌)
  let X := (Δ[0] : SSet.{u})
  let a : X ⟶ (Δ[1] : SSet.{u}) := stdSimplex.δ (1 : Fin 2)
  let b : X ⟶ (Δ[1] : SSet.{u}) := stdSimplex.δ (0 : Fin 2)
  let e := PreservesColimitPair.iso F X X
  have hd : ∀ x y, (F.map a) x ≠ (F.map b) y := by
    intro x y h
    have h₀ := congrArg (fun z : (Δ[1] : SSet.{u}) _⦋n⦌ ↦ z 0) h
    change ((stdSimplex.δ (1 : Fin 2)).app (Opposite.op ⦋n⦌) x) 0 =
      ((stdSimplex.δ (0 : Fin 2)).app (Opposite.op ⦋n⦌) y) 0 at h₀
    rw [stdSimplex.δ_one_eq_const, stdSimplex.δ_zero_eq_const] at h₀
    change (0 : Fin 2) = 1 at h₀
    exact Fin.zero_ne_one h₀
  have : Mono (coprod.desc (F.map a) (F.map b)) :=
    types_coprod_desc_mono _ _ ((mono_iff_injective _).mp inferInstance)
      ((mono_iff_injective _).mp inferInstance) hd
  have he : e.hom ≫ F.map (coprod.desc a b) = coprod.desc (F.map a) (F.map b) := by
    change coprod.desc (F.map coprod.inl) (F.map coprod.inr) ≫ F.map (coprod.desc a b) = _
    apply coprod.hom_ext
    · rw [coprod.inl_desc_assoc, ← F.map_comp, coprod.inl_desc, coprod.inl_desc]
    · rw [coprod.inr_desc_assoc, ← F.map_comp, coprod.inr_desc, coprod.inr_desc]
  have : Mono (e.hom ≫ F.map (coprod.desc a b)) := by rw [he]; infer_instance
  have hfac : F.map (coprod.desc a b) = e.inv ≫ (e.hom ≫ F.map (coprod.desc a b)) := by simp
  change Mono (F.map (coprod.desc a b))
  rw [hfac]
  infer_instance

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
