module
public import SerrePositivity.KST.SConstruction.CubeLeftKeep

/-! # 生成射での自然性から全立方体の語での自然性へ
概要：元の自由な生成語で、自然性を一文字の語から全体へ延長する。
方針：値域の圏を抽象化したまま、path の長さで帰納する。
規約：単体の語の射を元のまま保持する。使われ方：鎖立方体の tensor 比較の自然性。
-/
@[expose] public section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory

/-- 一文字の語での自然性を、元の全ての語へ延長する。 -/
lemma cubePath_naturality {V : Type*} [Quiver V] {C : Type u} [Category.{v} C]
    (F G : Paths V ⥤ C) (η : ∀ X, F.obj X ⟶ G.obj X)
    (h : ∀ {X Y : V} (g : X ⟶ Y), F.map g.toPath ≫ η Y = η X ≫ G.map g.toPath)
    {X Y : Paths V} (p : X ⟶ Y) : F.map p ≫ η Y = η X ≫ G.map p := by
  induction p with
  | nil =>
    change F.map (𝟙 X) ≫ η X = η X ≫ G.map (𝟙 X)
    rw [F.map_id, G.map_id, Category.id_comp, Category.comp_id]
  | cons p g ih =>
    let q := @Quiver.Hom.toPath V inferInstance _ _ g
    have hf := F.map_comp p q
    have hg := G.map_comp p q
    have hgen : F.map q ≫ η _ = η _ ≫ G.map q := h g
    calc
      _ = (F.map p ≫ F.map q) ≫ η _ := congrArg (fun f => f ≫ η _) hf
      _ = F.map p ≫ (F.map q ≫ η _) := Category.assoc _ _ _
      _ = F.map p ≫ (η _ ≫ G.map q) := congrArg (fun f => F.map p ≫ f) hgen
      _ = (F.map p ≫ η _) ≫ G.map q := (Category.assoc _ _ _).symm
      _ = (η _ ≫ G.map p) ≫ G.map q := congrArg (fun f => f ≫ G.map q) ih
      _ = η _ ≫ (G.map p ≫ G.map q) := Category.assoc _ _ _
      _ = _ := congrArg (fun f => η _ ≫ f) hg.symm


end SerrePositivity.KST.SConstruction
