module
public import SerrePositivity.CategoryTheory.ElementsChainLifting

/-! # 要素の反対圏の射列と最後のラベル
概要：反対圏の射列は底の射列と最後の係数ラベルから復元される。
方針：各頂点のラベルを最後のラベルから反変に運ぶ。
規約：射列を反転する選択や同型の置換はしない。使われ方：二重単体解消の転置行の余積表示。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory

/-- 概要：底の反対圏の射列と最後のラベルから要素の反対圏の射列を作る。
方針：最後への射を反転して係数を各頂点へ運ぶ。
規約：全頂点と全射を同時に構成。使われ方：解消の行の余積表示の逆射。 -/
def oppositeLabelledChainLift {J : Type u} [Category.{v} J] (F : J ⥤ Type w) {n : ℕ}
    (c : ComposableArrows Jᵒᵖ n) (x : F.obj (c.obj (Fin.last n)).unop) :
    ComposableArrows F.Elementsᵒᵖ n where
  obj i := Opposite.op (F.elementsMk (c.obj i).unop
    (F.map (c.map (homOfLE (Fin.le_last i))).unop x))
  map {i j} h := (Functor.Elements.homMk (c.map h).unop (by
    change F.map (c.map h).unop (F.map (c.map (homOfLE (Fin.le_last j))).unop x) = _
    rw [← ConcreteCategory.comp_apply, ← F.map_comp]
    change F.map (c.map h ≫ c.map (homOfLE (Fin.le_last j))).unop x = _
    rw [← c.map_comp]
    rfl)).op
  map_id i := by
    apply Quiver.Hom.unop_inj
    apply Functor.Elements.hom_ext
    exact congrArg Quiver.Hom.unop (c.map_id i)
  map_comp h k := by
    apply Quiver.Hom.unop_inj
    apply Functor.Elements.hom_ext
    exact congrArg Quiver.Hom.unop (c.map_comp h k)

/-- 概要：任意の要素の反対圏の射列は底の射列と最後のラベルから復元される。
方針：各頂点のラベル条件と射の忘却の忠実性を使う。
規約：射列全体の厳密な等号。使われ方：行の同型の逆律。 -/
lemma oppositeLabelledChain_reconstruct {J : Type u} [Category.{v} J] (F : J ⥤ Type w)
    {n : ℕ} (c : ComposableArrows F.Elementsᵒᵖ n) :
    oppositeLabelledChainLift F (c ⋙ (Functor.Elements.π F).op)
      (c.obj (Fin.last n)).unop.val = c := by
  refine CategoryTheory.Functor.ext (fun i => ?_) ?_
  · change Opposite.op _ = Opposite.op (c.obj i).unop
    congr 1
    change F.elementsMk (c.obj i).unop.obj
      (F.map (c.map (homOfLE (Fin.le_last i))).unop.hom
        (c.obj (Fin.last n)).unop.val) = (c.obj i).unop
    refine Functor.Elements.ext _ _ rfl ?_
    change F.map (𝟙 _) (F.map (c.map (homOfLE (Fin.le_last i))).unop.hom
      (c.obj (Fin.last n)).unop.val) = (c.obj i).unop.val
    rw [F.map_id, types_id_apply]
    exact (c.map (homOfLE (Fin.le_last i))).unop.map_val
  · intro i j h
    apply Quiver.Hom.unop_inj
    apply Functor.Elements.hom_ext
    simp [oppositeLabelledChainLift, SerrePositivity.LabelledChain.eqToHom_hom]

/-- 概要：要素の反対圏の射列と底の射列・最後のラベルの対の同値。
方針：元の射列を射影し、最後からのラベル輸送で戻す。
規約：宇宙は元の圏と係数のまま。使われ方：転置行の実際の余積との比較。 -/
def oppositeLabelledChainEquiv {J : Type u} [Category.{v} J] (F : J ⥤ Type w) (n : ℕ) :
    ComposableArrows F.Elementsᵒᵖ n ≃
      Σ c : ComposableArrows Jᵒᵖ n, F.obj (c.obj (Fin.last n)).unop where
  toFun c := ⟨c ⋙ (Functor.Elements.π F).op, (c.obj (Fin.last n)).unop.val⟩
  invFun s := oppositeLabelledChainLift F s.1 s.2
  left_inv c := oppositeLabelledChain_reconstruct F c
  right_inv s := by
    rcases s with ⟨c, x⟩
    refine Sigma.ext (CategoryTheory.Functor.ext (fun _ => rfl)) ?_
    apply heq_of_eq
    change F.map (c.map (𝟙 _)).unop x = x
    rw [c.map_id]
    change F.map (𝟙 _) x = x
    rw [F.map_id]
    rfl

end SerrePositivity.KST.SConstruction
