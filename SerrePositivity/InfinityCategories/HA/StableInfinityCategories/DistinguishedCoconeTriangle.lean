module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Triangulated
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberShortComplex

/-! # 任意の射を含む cofiber 三角形

概要：h C の任意の射を第一射とする cofiber distinguished triangle が存在する。
方針：既存の cofiber 短複体の存在を使い、Arrow の等号から両端と第一射を指定する。
規約：TR1 の射を含む三角形の存在部分。恒等射の三角形の判定は別途必要。
使われ方：S4 の Pretriangulated.distinguished_cocone_triangle の候補の証明。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Pretriangulated SSet
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：任意の射 f を第一射に持つ cofiber distinguished triangle が存在する。
方針：短複体の第一射との Arrow の等号で端点を置き換え、cofiberTriangle を取る。
規約：対象と第一射を厳密に指定する。使われ方：TR1 の存在部分。 -/
lemma exists_cofiberDistinguishedTriangle {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    {a b : hoFunctor.obj X} (f : a ⟶ b) :
    ∃ (z : hoFunctor.obj X) (g : b ⟶ z) (h : z ⟶ (shiftFunctor (hoFunctor.obj X) (1 : ℤ)).obj a),
      Triangle.mk f g h ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberDistinguishedTriangles X := by
  obtain ⟨t, ht, he⟩ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.exists_cofiber_hoShortComplex f
  obtain ⟨ha, hb, hf⟩ := (Arrow.mk_eq_mk_iff _ _).mp he
  subst a b
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hf
  subst f
  exact ⟨t.hoShortComplex.X₃, t.hoShortComplex.g, (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberTriangle t ht).mor₃,
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberTriangle_mem_cofiberDistinguishedTriangles t ht⟩

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
