module

public import SerrePositivity.InfinityCategories.F1.FiberTransportFamilySourceComparison
public import SerrePositivity.InfinityCategories.F1.VertexFiberTotalIso
public import SerrePositivity.InfinityCategories.HomotopyLimits.FibersBaseIso

/-!
概要：底を変更する可換正方形による輸送族の後合成。
方針：部分型の fiber の直接の誘導射で両端を移し、prism を全空間の射で後合成する。
規約：正方形の可換性は厳密な等式。モデル構造は用いない。
使われ方：普遍 coslice 輸送の同値性を pointed-space 射影へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：底も動かす可換正方形の直接の fiber 射。
方針：元の fiber から全空間を経由し、標的の fiber へ持ち上げる。
規約：fibration 性や Kan 性は不要。
使われ方：輸送族の始点と終点の後合成。 -/
def transportSquareFiberMap {E B F D : SSet.{u}} (p : E ⟶ B) (q : F ⟶ D)
    (f : E ⟶ F) (g : B ⟶ D) (h : f ≫ q = p ≫ g) (b : B _⦋0⦌) :
    vertexFiber p b ⟶ vertexFiber q (g.app _ b) :=
  vertexFiberLift q (g.app _ b) (vertexFiberι p b ≫ f) (by
    rw [Category.assoc, h, ← Category.assoc, vertexFiberι_comp, SSet.const_comp])

/-- 概要：正方形の fiber 射は元の全空間への包含と可換。
方針：fiber の持ち上げの包含の式を読む。
規約：任意の高次単体を保つ厳密な等式。
使われ方：輸送族の両端の可換性。 -/
lemma transportSquareFiberMap_ι {E B F D : SSet.{u}} (p : E ⟶ B) (q : F ⟶ D)
    (f : E ⟶ F) (g : B ⟶ D) (h : f ≫ q = p ≫ g) (b : B _⦋0⦌) :
    transportSquareFiberMap p q f g h b ≫ vertexFiberι q (g.app _ b) =
      vertexFiberι p b ≫ f := rfl

/-- 概要：底と全空間の同型の正方形の fiber 射は同型。
方針：底の変更と底を固定した全空間の同型の fiber 同型を合成する。
規約：fiber の直接の射そのものの同型性。
使われ方：同型による普遍輸送の移送で係数比較を消去する。 -/
lemma transportSquareFiberMap_isIso {E B F D : SSet.{u}} (p : E ⟶ B) (q : F ⟶ D)
    (e : E ≅ F) (d : B ≅ D) (h : e.hom ≫ q = p ≫ d.hom) (b : B _⦋0⦌) :
    IsIso (transportSquareFiberMap p q e.hom d.hom h b) := by
  let i := HomotopyLimits.vertexFiberBaseIso p d b ≪≫
    vertexFiberTotalIso (p ≫ d.hom) q e h (d.hom.app _ b)
  have hi : transportSquareFiberMap p q e.hom d.hom h b = i.hom := rfl
  rw [hi]
  infer_instance

/-- 概要：輸送族を底を動かす可換正方形で後合成する。
方針：両端は fiber 射、prism は全空間の射、底の族は底の射で移す。
規約：係数とパラメーター自体は保つ。
使われ方：既存の普遍輸送を新しい射影の輸送と比較する。 -/
def FiberTransportFamily.pushforward {E B F D K L : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ D) (f : E ⟶ F) (g : B ⟶ D) (h : f ≫ q = p ≫ g)
    {a b : B _⦋0⦌} {k : K ⟶ vertexFiber p a} {γ : Δ[1] ⊗ L ⟶ B}
    (T : FiberTransportFamily (b := b) p k γ) :
    FiberTransportFamily (b := g.app _ b) q (k ≫ transportSquareFiberMap p q f g h a) (γ ≫ g) where
  endpoint := T.endpoint ≫ transportSquareFiberMap p q f g h b
  prism := T.prism ≫ f
  start := by
    rw [← Category.assoc, T.start]
    simp only [Category.assoc, transportSquareFiberMap_ι]
  finish := by
    rw [← Category.assoc, T.finish]
    simp only [Category.assoc, transportSquareFiberMap_ι]
  over_base := by
    rw [Category.assoc, h, ← Category.assoc, T.over_base, Category.assoc]

/-- 概要：輸送族の後合成の curry は fiber 射の内部 Hom の後合成。
方針：終点の curry の終域に関する自然性を使う。
規約：全パラメーター上での厳密な射の等式。
使われ方：普遍輸送の自然性の関手同型の左辺。 -/
lemma FiberTransportFamily.pushforward_map {E B F D K L : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ D) (f : E ⟶ F) (g : B ⟶ D) (h : f ≫ q = p ≫ g)
    {a b : B _⦋0⦌} {k : K ⟶ vertexFiber p a} {γ : Δ[1] ⊗ L ⟶ B}
    (T : FiberTransportFamily (b := b) p k γ) :
    (T.pushforward p q f g h).map =
      T.map ≫ (ihom K).map (transportSquareFiberMap p q f g h b) :=
  curry_natural_right _ _

end SerrePositivity.InfinityCategories
