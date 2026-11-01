module

public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.ComparisonTriangleHorn

/-!
# 中断した任意モデル源への一般化：KanComparisonTetrahedron

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Three specified comparison triangles extend to one tetrahedron。

## 方針（定義・証明）
全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0408][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0408
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Three specified comparison triangles extend to one tetrahedron

The three cone faces share their original whole edges to the common
endpoint. Their compatibility therefore follows from the triangle data,
without changing any selected triangle. The fourth face retains all
three previously selected comparison edges.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open scoped SSet.modelCategoryQuillen

namespace SerrePositivity.SimplicialModel.KanComparisonTetrahedron
open KanComparisonTriangle
variable {T K : SSet.{v}} {f g h z : T ⟶ K}
  (F : SSet.Homotopy f z) (G : SSet.Homotopy g z) (H : SSet.Homotopy h z)
  (a : Data F G) (b : Data F H) (c : Data G H)

abbrev hornFaces : ∀ (j : Fin 4) (_ : j ≠ 3),
    SSet.stdSimplex.obj (SimplexCategory.mk 2) ⟶ (ihom T).obj K :=
  fun j _ => if j = 0 then c.triangle else if j = 1 then b.triangle else a.triangle

lemma hornCompatible : SSet.horn.IsCompatible (hornFaces F G H a b c) := by
  intro j k hj hk hjk
  fin_cases j <;> fin_cases k <;> first
  | exact (hj rfl).elim
  | exact (hk rfl).elim
  | exact ((not_lt_of_ge (by decide)) hjk).elim
  | exact c.face_zero.trans b.face_zero.symm
  | exact c.face_one.trans a.face_zero.symm
  | exact b.face_one.trans a.face_one.symm

abbrev hornMap : (SSet.horn.{v} 3 3).toSSet ⟶ (ihom T).obj K :=
  (hornCompatible F G H a b c).desc

lemma hornMap_zero : SSet.horn.ι (3 : Fin 4) 0 (by decide) ≫ hornMap F G H a b c =
    c.triangle := (hornCompatible F G H a b c).ι_desc 0 (by decide)

lemma hornMap_one : SSet.horn.ι (3 : Fin 4) 1 (by decide) ≫ hornMap F G H a b c =
    b.triangle := (hornCompatible F G H a b c).ι_desc 1 (by decide)

lemma hornMap_two : SSet.horn.ι (3 : Fin 4) 2 (by decide) ≫ hornMap F G H a b c =
    a.triangle := (hornCompatible F G H a b c).ι_desc 2 (by decide)

structure Filler where
  tetrahedron : SSet.stdSimplex.obj (SimplexCategory.mk 3) ⟶ (ihom T).obj K
  face_zero : SSet.stdSimplex.δ (0 : Fin 4) ≫ tetrahedron = c.triangle
  face_one : SSet.stdSimplex.δ (1 : Fin 4) ≫ tetrahedron = b.triangle
  face_two : SSet.stdSimplex.δ (2 : Fin 4) ≫ tetrahedron = a.triangle

variable (hK : SSet.modelCategoryQuillen.J.rlp (terminal.from K))

def build : Filler F G H a b c := by
  let p := terminal.from ((ihom T).obj K)
  have : HomotopicalAlgebra.Fibration p :=
    (SSet.modelCategoryQuillen.fibration_iff p).mpr (SimplexParameterHom.native_kan T K hK)
  let e := (hornCompatible F G H a b c).exists_lift p (terminal.from _)
    (fun _ _ => terminal.hom_ext _ _)
  exact ⟨e.choose, e.choose_spec.1 0 (by decide), e.choose_spec.1 1 (by decide),
    e.choose_spec.1 2 (by decide)⟩

variable (d : Filler F G H a b c)

abbrev triangle : SSet.stdSimplex.obj (SimplexCategory.mk 2) ⟶ (ihom T).obj K :=
  SSet.stdSimplex.δ (3 : Fin 4) ≫ d.tetrahedron

private lemma face_swap (i : Fin 3) :
    SSet.stdSimplex.δ.{v} i ≫ SSet.stdSimplex.δ (3 : Fin 4) =
      SSet.stdSimplex.δ (2 : Fin 3) ≫ SSet.stdSimplex.δ i.castSucc := by
  change SSet.stdSimplex.map _ ≫ SSet.stdSimplex.map _ =
    SSet.stdSimplex.map _ ≫ SSet.stdSimplex.map _
  rw [← SSet.stdSimplex.map_comp, ← SSet.stdSimplex.map_comp]
  apply congrArg SSet.stdSimplex.map
  fin_cases i <;> decide

lemma triangle_zero : SSet.stdSimplex.δ (0 : Fin 3) ≫ triangle F G H a b c d =
    SSet.stdSimplex.δ (2 : Fin 3) ≫ c.triangle := by
  rw [triangle, ← Category.assoc, face_swap, Category.assoc]
  exact congrArg (fun q => SSet.stdSimplex.δ (2 : Fin 3) ≫ q) d.face_zero

lemma triangle_one : SSet.stdSimplex.δ (1 : Fin 3) ≫ triangle F G H a b c d =
    SSet.stdSimplex.δ (2 : Fin 3) ≫ b.triangle := by
  rw [triangle, ← Category.assoc, face_swap, Category.assoc]
  exact congrArg (fun q => SSet.stdSimplex.δ (2 : Fin 3) ≫ q) d.face_one

lemma triangle_two : SSet.stdSimplex.δ (2 : Fin 3) ≫ triangle F G H a b c d =
    SSet.stdSimplex.δ (2 : Fin 3) ≫ a.triangle := by
  rw [triangle, ← Category.assoc, face_swap, Category.assoc]
  exact congrArg (fun q => SSet.stdSimplex.δ (2 : Fin 3) ≫ q) d.face_two

abbrev family : T ⊗ SSet.stdSimplex.obj (SimplexCategory.mk 3) ⟶ K := uncurry d.tetrahedron

lemma family_zero : T ◁ SSet.stdSimplex.δ (0 : Fin 4) ≫ family F G H a b c d =
    KanComparisonTriangle.family G H c := by
  rw [family, ← uncurry_natural_left, d.face_zero]

lemma family_one : T ◁ SSet.stdSimplex.δ (1 : Fin 4) ≫ family F G H a b c d =
    KanComparisonTriangle.family F H b := by
  rw [family, ← uncurry_natural_left, d.face_one]

lemma family_two : T ◁ SSet.stdSimplex.δ (2 : Fin 4) ≫ family F G H a b c d =
    KanComparisonTriangle.family F G a := by
  rw [family, ← uncurry_natural_left, d.face_two]

abbrev coherence : T ⊗ SSet.stdSimplex.obj (SimplexCategory.mk 2) ⟶ K :=
  uncurry (triangle F G H a b c d)

lemma coherence_zero : T ◁ SSet.stdSimplex.δ (0 : Fin 3) ≫ coherence F G H a b c d =
    (comparison G H c).h := by
  rw [coherence, ← uncurry_natural_left, triangle_zero]
  rfl

lemma coherence_one : T ◁ SSet.stdSimplex.δ (1 : Fin 3) ≫ coherence F G H a b c d =
    (comparison F H b).h := by
  rw [coherence, ← uncurry_natural_left, triangle_one]
  rfl

lemma coherence_two : T ◁ SSet.stdSimplex.δ (2 : Fin 3) ≫ coherence F G H a b c d =
    (comparison F G a).h := by
  rw [coherence, ← uncurry_natural_left, triangle_two]
  rfl

end SerrePositivity.SimplicialModel.KanComparisonTetrahedron
