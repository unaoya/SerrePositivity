module
public import Mathlib.CategoryTheory.Triangulated.Triangulated

/-! # 三角形比較からの八面体の組み立て

概要：二つの三角形の射と最後の三角形の所属を、対象表示をそろえて八面体にまとめる。
方針：Arrow の等号から対象の等号を消去し、四つの可換式を二つの三角形の射から取る。
規約：任意の前三角圏を扱い、八面体公理は仮定しない。使われ方：安定 ∞ 圏の TR4。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory Pretriangulated Triangulated Limits
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：指定した二つの Arrow と同じ第一辺を持つ八面体の具体的な模型が存在する。
方針：六対象、三つの distinguished 三角形、四可換式と最後の三角形の所属を保持する。
規約：模型は元の対象と等号で比較できる。使われ方：任意の入力への同型輸送。 -/
def OctahedronModel {C : Type u} [Category.{v} C]
    [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] (p q : Arrow C) : Prop :=
  ∃ (A B D Z₁₂ Z₂₃ Z₁₃ : C) (f : A ⟶ B) (g : B ⟶ D)
      (v₁₂ : B ⟶ Z₁₂) (w₁₂ : Z₁₂ ⟶ (shiftFunctor C (1 : ℤ)).obj A)
      (v₂₃ : D ⟶ Z₂₃) (w₂₃ : Z₂₃ ⟶ (shiftFunctor C (1 : ℤ)).obj B)
      (v₁₃ : D ⟶ Z₁₃) (w₁₃ : Z₁₃ ⟶ (shiftFunctor C (1 : ℤ)).obj A)
      (H₁₂ : Triangle.mk f v₁₂ w₁₂ ∈ distTriang C)
      (H₂₃ : Triangle.mk g v₂₃ w₂₃ ∈ distTriang C)
      (H₁₃ : Triangle.mk (f ≫ g) v₁₃ w₁₃ ∈ distTriang C),
      Arrow.mk f = p ∧ Arrow.mk g = q ∧
        Nonempty (Octahedron rfl H₁₂ H₂₃ H₁₃)

/-- 概要：端点を含む成分の照合を持つ二つの比較は、共通の対象表示の八面体を与える。
方針：恒等成分と射の Arrow の等号で対象と射を置き換え、最後の三角形の所属を移す。
規約：出力の最初の二射は入力の最初の二射と Arrow として等しい。
使われ方：幾何学的な二長方形から Mathlib の八面体を得る。 -/
lemma exists_octahedron_of_triangle_comparisons {C : Type u} [Category.{v} C]
    [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (T₁₂ T₁₃ T₂₃ T₄ : Triangle C)
    (h₁₂ : T₁₂ ∈ distTriang C) (h₁₃ : T₁₃ ∈ distTriang C)
    (h₂₃ : T₂₃ ∈ distTriang C) (h₄ : T₄ ∈ distTriang C)
    (a : T₁₂ ⟶ T₁₃) (b : T₁₃ ⟶ T₂₃) (s : T₂₃.obj₁ ⟶ T₄.obj₁)
    (ha₁ : Arrow.mk a.hom₁ = Arrow.mk (𝟙 T₁₂.obj₁))
    (ha₂ : Arrow.mk a.hom₂ = Arrow.mk T₂₃.mor₁)
    (hb₁ : Arrow.mk b.hom₁ = Arrow.mk T₁₂.mor₁)
    (hb₂ : Arrow.mk b.hom₂ = Arrow.mk (𝟙 T₁₃.obj₂))
    (hk : Arrow.mk T₄.mor₁ = Arrow.mk a.hom₃)
    (hl : Arrow.mk T₄.mor₂ = Arrow.mk b.hom₃)
    (hs : Arrow.mk s = Arrow.mk T₁₂.mor₂)
    (hw : Arrow.mk T₄.mor₃ = Arrow.mk
      (T₂₃.mor₃ ≫ (shiftFunctor C (1 : ℤ)).map s)) :
    OctahedronModel (Arrow.mk T₁₂.mor₁) (Arrow.mk T₂₃.mor₁) := by
  dsimp only [OctahedronModel]
  rcases T₁₂ with ⟨A, B, Z₁₂, f, v₁₂, w₁₂⟩
  rcases T₁₃ with ⟨A', D, Z₁₃, h, v₁₃, w₁₃⟩
  rcases T₂₃ with ⟨B', D', Z₂₃, g, v₂₃, w₂₃⟩
  rcases T₄ with ⟨Z₁₂', Z₁₃', Z₂₃', k, l, w₄⟩
  obtain ⟨_, hA, _⟩ := (Arrow.mk_eq_mk_iff _ _).mp ha₁
  change A' = A at hA
  subst A'
  obtain ⟨_, hD, _⟩ := (Arrow.mk_eq_mk_iff _ _).mp hb₂
  change D' = D at hD
  subst D'
  obtain ⟨hB, _, _⟩ := (Arrow.mk_eq_mk_iff _ _).mp ha₂
  change B = B' at hB
  subst B'
  obtain ⟨hZ₁₂, hZ₁₃, _⟩ := (Arrow.mk_eq_mk_iff _ _).mp hk
  change Z₁₂' = Z₁₂ at hZ₁₂
  change Z₁₃' = Z₁₃ at hZ₁₃
  subst Z₁₂' Z₁₃'
  obtain ⟨_, hZ₂₃, _⟩ := (Arrow.mk_eq_mk_iff _ _).mp hl
  change Z₂₃' = Z₂₃ at hZ₂₃
  subst Z₂₃'
  have ha₁' : a.hom₁ = 𝟙 A := Arrow.mk_injective _ _ ha₁
  have ha₂' : a.hom₂ = g := Arrow.mk_injective _ _ ha₂
  have hb₁' : b.hom₁ = f := Arrow.mk_injective _ _ hb₁
  have hb₂' : b.hom₂ = 𝟙 D := Arrow.mk_injective _ _ hb₂
  have hk' : k = a.hom₃ := Arrow.mk_injective _ _ hk
  have hl' : l = b.hom₃ := Arrow.mk_injective _ _ hl
  have hs' : s = v₁₂ := Arrow.mk_injective _ _ hs
  have hw' : w₄ = w₂₃ ≫ (shiftFunctor C (1 : ℤ)).map s := Arrow.mk_injective _ _ hw
  change Triangle.mk k l w₄ ∈ distTriang C at h₄
  rw [hk', hl', hw', hs'] at h₄
  have hfg : f ≫ g = h := by
    have hh := a.comm₁
    simpa only [ha₁', ha₂', Category.id_comp] using hh
  subst h
  refine ⟨A, B, D, Z₁₂, Z₂₃, Z₁₃, f, g, v₁₂, w₁₂, v₂₃, w₂₃, v₁₃, w₁₃,
    h₁₂, h₂₃, h₁₃, rfl, rfl, ⟨⟨a.hom₃, b.hom₃, ?_, ?_, ?_, ?_, h₄⟩⟩⟩
  · simpa only [ha₂'] using a.comm₂
  · have hh := a.comm₃
    rw [ha₁', CategoryTheory.Functor.map_id, Category.comp_id] at hh
    exact hh.symm
  · simpa only [hb₂', Category.id_comp] using b.comm₂
  · simpa only [hb₁'] using b.comm₃

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
