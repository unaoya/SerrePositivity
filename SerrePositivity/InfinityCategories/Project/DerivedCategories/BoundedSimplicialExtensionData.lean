module
public import Mathlib.AlgebraicTopology.SimplicialSet.Splitting
public import Mathlib.AlgebraicTopology.SimplicialSet.Dimension

/-! # 有界な単体集合上の切断写像の次数別延長

概要：非退化単体の次元上界から、切断写像を全次数の写像へ延長する。
方針：標準 splitting の直和表示上で退化の引き戻しを定義する。
規約：自然性は後続ファイルで証明する。使われ方：有限図式の錐を実 join へ移す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet Opposite
open scoped _root_.Simplicial
variable {K Y : SSet.{u}} {N : ℕ} [K.HasDimensionLE N]
variable (F : (truncation N).obj K ⟶ (truncation N).obj Y)

/-- 非退化単体の引き戻し上に定義した、全次数の写像。 -/
def boundedSimplicialExtensionApp (a : SimplexCategoryᵒᵖ) : K.obj a ⟶ Y.obj a :=
  K.splitting.desc a (fun B => ↾fun y => Y.map B.e.op
    (F.app (op ⟨B.1.unop, K.dim_le_of_nonDegenerate y N⟩) y.val))

/-- 非退化単体の任意の全射表示上で延長の値は指定値の引き戻しになる。 -/
lemma boundedSimplicialExtensionApp_nondegenerate {n m : ℕ}
    (β : ⦋n⦌ ⟶ ⦋m⦌) [Epi β] (y : K.nonDegenerate m) :
    boundedSimplicialExtensionApp F (op ⦋n⦌) (K.map β.op y.val) =
      Y.map β.op (F.app (op ⟨⦋m⦌, K.dim_le_of_nonDegenerate y N⟩) y.val) := by
  have h := ConcreteCategory.congr_hom (K.splitting.ι_desc (op ⦋n⦌)
    (fun B => ↾fun z => Y.map B.e.op
      (F.app (op ⟨B.1.unop, K.dim_le_of_nonDegenerate z N⟩) z.val))
    (.mk β)) y
  exact h

/-- 指定上界以内の次数では、延長は元の切断写像と厳密に一致する。 -/
lemma boundedSimplicialExtensionApp_low {n : ℕ} (hn : n ≤ N) (σ : K _⦋n⦌) :
    boundedSimplicialExtensionApp F (op ⦋n⦌) σ = F.app (op ⟨⦋n⦌, hn⟩) σ := by
  obtain ⟨m, β, hβ, y, rfl⟩ := K.exists_nonDegenerate σ
  rw [boundedSimplicialExtensionApp_nondegenerate]
  have h := ConcreteCategory.congr_hom (F.naturality
    (SimplexCategory.Truncated.Hom.tr β (ha := hn)
      (hb := K.dim_le_of_nonDegenerate y N)).op) y.val
  exact h.symm

/-- 任意の低次数単体の全射表示上でも同じ引き戻し公式が成立する。 -/
lemma boundedSimplicialExtensionApp_epi {n m : ℕ} (hm : m ≤ N)
    (β : ⦋n⦌ ⟶ ⦋m⦌) [Epi β] (y : K _⦋m⦌) :
    boundedSimplicialExtensionApp F (op ⦋n⦌) (K.map β.op y) =
      Y.map β.op (F.app (op ⟨⦋m⦌, hm⟩) y) := by
  obtain ⟨p, γ, hγ, z, rfl⟩ := K.exists_nonDegenerate y
  have h := ConcreteCategory.congr_hom (F.naturality
    (SimplexCategory.Truncated.Hom.tr γ (ha := hm)
      (hb := K.dim_le_of_nonDegenerate z N)).op) z.val
  change F.app (op ⟨⦋m⦌, hm⟩) (K.map γ.op z.val) =
    Y.map γ.op (F.app (op ⟨⦋p⦌, K.dim_le_of_nonDegenerate z N⟩) z.val) at h
  calc
    _ = boundedSimplicialExtensionApp F (op ⦋n⦌) (K.map (β ≫ γ).op z.val) := by
      rw [op_comp, Functor.map_comp_apply]
    _ = Y.map (β ≫ γ).op
        (F.app (op ⟨⦋p⦌, K.dim_le_of_nonDegenerate z N⟩) z.val) :=
      boundedSimplicialExtensionApp_nondegenerate F (β ≫ γ) z
    _ = Y.map β.op (Y.map γ.op
        (F.app (op ⟨⦋p⦌, K.dim_le_of_nonDegenerate z N⟩) z.val)) := by
      rw [op_comp, Functor.map_comp_apply]
    _ = _ := congrArg (Y.map β.op) h.symm

end SerrePositivity.InfinityCategories.Project.DerivedCategories
