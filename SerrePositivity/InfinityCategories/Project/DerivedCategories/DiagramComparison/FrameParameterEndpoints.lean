module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.FrameParameterEvaluation
/-!
概要：指定余作用の単位則から区間パラメータの端点評価を得る。
方針：同じ増大写像と端点への分解をテンソルで合成する。
規約：A07両端評価の証明分割。単位則と指定射を型に保持する。
使われ方：HA 1.2.4、全単体Homの元の二射への一致。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable {F G P : SimplexCategory ⥤ C}
/-- 指定単位則と区間端点の等式は同じframe評価の端点を与える。 -/
theorem frameParameterEvaluation_endpoint
    (δ : F ⟶ F ⊗ P) (α : P ⟶ 𝟙_ (SimplexCategory ⥤ C))
    (hδ : δ ≫ (𝟙 F ⊗ₘ α) ≫ (ρ_ F).hom = 𝟙 F)
    (k : F ⊗ (Functor.const SimplexCategory).obj (P.obj ⦋1⦌) ⟶ G)
    (e : 𝟙_ C ⟶ P.obj ⦋1⦌) (f : F ⟶ G)
    (hk : (ρ_ F).inv ≫ (𝟙 F ⊗ₘ (Functor.const SimplexCategory).map e) ≫ k = f)
    (n : SimplexCategory) (t : n ⟶ ⦋1⦌) (ht : P.map t = α.app n ≫ e) :
    frameParameterEvaluation δ k n t = f.app n := by
  have hc := NatTrans.congr_app hδ n
  change δ.app n ≫ (𝟙 (F.obj n) ⊗ₘ α.app n) ≫ (ρ_ (F.obj n)).hom = 𝟙 _ at hc
  rw [id_tensorHom] at hc
  have he : (F.obj n ◁ e) ≫ k.app n = (ρ_ (F.obj n)).hom ≫ f.app n := by
    apply (cancel_epi (ρ_ (F.obj n)).inv).mp
    have hh := NatTrans.congr_app hk n
    change (ρ_ (F.obj n)).inv ≫ (𝟙 (F.obj n) ⊗ₘ e) ≫ k.app n = f.app n at hh
    rw [id_tensorHom] at hh
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using hh
  dsimp only [frameParameterEvaluation]
  rw [ht, whiskerLeft_comp]
  simp only [Category.assoc]
  rw [he]
  simpa only [Category.assoc, Category.id_comp] using congrArg (fun z => z ≫ f.app n) hc
end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
