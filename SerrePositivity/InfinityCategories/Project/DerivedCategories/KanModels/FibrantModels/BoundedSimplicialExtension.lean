module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.FibrantModels.BoundedSimplicialExtensionData

/-! # 次元上界を持つ単体集合の切断写像の延長

概要：上界までの自然変換は全単体集合上の一意な自然変換へ延長する。
方針：任意の射を全射・単射へ分解し、非退化表示上の公式と切断自然性を使う。
規約：標的の quasicategory 性は不要。使われ方：有限図式の実 join 錐。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet Opposite Limits
open scoped _root_.Simplicial
variable {K Y : SSet.{u}} {N : ℕ} [K.HasDimensionLE N]
variable (F : (truncation N).obj K ⟶ (truncation N).obj Y)

/-- 次数別延長は任意の単体圏の射に自然。 -/
lemma boundedSimplicialExtensionApp_naturality {n m : ℕ}
    (α : ⦋n⦌ ⟶ ⦋m⦌) (σ : K _⦋m⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.boundedSimplicialExtensionApp F (op ⦋n⦌) (K.map α.op σ) =
      Y.map α.op (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.boundedSimplicialExtensionApp F (op ⦋m⦌) σ) := by
  obtain ⟨l, β, hβ, z, rfl⟩ := K.exists_nonDegenerate σ
  let g := α ≫ β
  have hq : (image g).len ≤ N :=
    (SimplexCategory.len_le_of_mono (image.ι g)).trans (K.dim_le_of_nonDegenerate z N)
  have hF := ConcreteCategory.congr_hom (F.naturality
    (SimplexCategory.Truncated.Hom.tr (image.ι g) (ha := hq)
      (hb := K.dim_le_of_nonDegenerate z N)).op) z.val
  change F.app (op ⟨image g, hq⟩) (K.map (image.ι g).op z.val) =
    Y.map (image.ι g).op (F.app (op ⟨⦋l⦌, K.dim_le_of_nonDegenerate z N⟩) z.val) at hF
  have hmap : K.map (factorThruImage g).op (K.map (image.ι g).op z.val) =
      K.map (α ≫ β).op z.val := by
    rw [← Functor.map_comp_apply, ← op_comp, image.fac]
  calc
    _ = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.boundedSimplicialExtensionApp F (op ⦋n⦌)
        (K.map (factorThruImage g).op (K.map (image.ι g).op z.val)) := by
      rw [hmap, op_comp, Functor.map_comp_apply]
    _ = Y.map (factorThruImage g).op
        (F.app (op ⟨image g, hq⟩) (K.map (image.ι g).op z.val)) :=
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.boundedSimplicialExtensionApp_epi F hq (factorThruImage g) _
    _ = Y.map (factorThruImage g).op (Y.map (image.ι g).op
        (F.app (op ⟨⦋l⦌, K.dim_le_of_nonDegenerate z N⟩) z.val)) :=
      congrArg (Y.map (factorThruImage g).op) hF
    _ = Y.map α.op (Y.map β.op
        (F.app (op ⟨⦋l⦌, K.dim_le_of_nonDegenerate z N⟩) z.val)) := by
      rw [← Functor.map_comp_apply, ← op_comp, image.fac]
      change Y.map (α ≫ β).op _ = _
      rw [op_comp, Functor.map_comp_apply]
    _ = _ := by rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.boundedSimplicialExtensionApp_nondegenerate]

/-- 次元上界までの切断写像から得られる全単体集合上の実写像。 -/
def boundedSimplicialExtension : K ⟶ Y where
  app := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.boundedSimplicialExtensionApp F
  naturality a b α := by
    apply ConcreteCategory.hom_ext
    intro σ
    exact boundedSimplicialExtensionApp_naturality F α.unop σ

/-- 延長を上界まで切断すると、元の自然変換に厳密に戻る。 -/
lemma boundedSimplicialExtension_truncation :
    (truncation N).map (boundedSimplicialExtension F) = F := by
  ext a σ
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.boundedSimplicialExtensionApp_low F a.unop.property σ

/-- 次元上界以下で一致する二つの単体写像は全次数で一致する。 -/
lemma boundedSimplicialHom_ext (G H : K ⟶ Y)
    (h : (truncation N).map G = (truncation N).map H) : G = H := by
  apply K.splitting.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro y
  exact ConcreteCategory.congr_hom (congr_app h (op ⟨⦋n⦌, K.dim_le_of_nonDegenerate y N⟩)) y.val

/-- 切断写像の全次数への延長は一意。 -/
lemma boundedSimplicialExtension_unique (G : K ⟶ Y) (h : (truncation N).map G = F) :
    G = boundedSimplicialExtension F :=
  boundedSimplicialHom_ext G _ (h.trans (boundedSimplicialExtension_truncation F).symm)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
