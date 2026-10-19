module

public import SerrePositivity.InfinityCategories.F2.CoproductPrismVertical

/-!
概要：時刻に定値な prism の端点と可逆な垂直辺。
方針：第二射影と定値単体の自然性を計算する。
規約：時刻の標準区間は第一因子。
使われ方：錐の頂点を固定した指定自然変換の延長。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：定値 prism の両端点は元の射。
方針：第二射影と端点包含の合成を計算する。
規約：同じ式で両端点を扱う。
使われ方：錐の頂点を全時刻で固定する条件。 -/
lemma constantPrism_endpoint {A X : SSet.{u}} (f : A ⟶ X) (k : Fin 2) :
    prismEndpoint k A ≫ (snd Δ[1] A ≫ f) = f := by
  rw [← Category.assoc]
  change (lift (SSet.const (stdSimplex.obj₀Equiv.symm k)) (𝟙 A) ≫ snd Δ[1] A) ≫ f = f
  rw [lift_snd, Category.id_comp]
/-- 概要：定値 prism の垂直辺は全て可逆。
方針：定値一次単体の自然性と恒等辺の可逆性を使う。
規約：標的の quasicategory 性は不要。
使われ方：頂点を固定した図式円柱の貼り合わせ。 -/
lemma constantPrism_vertical_isInvertible {A X : SSet.{u}} (f : A ⟶ X) (x : A _⦋0⦌) :
    IsInvertibleEdge (edgeOfSimplex ((snd Δ[1] A ≫ f).app (Opposite.op ⦋1⦌)
      (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), PinchedHom.constant x 1))) := by
  have h := ConcreteCategory.congr_hom
    (f.naturality (SimplexCategory.const ⦋1⦌ ⦋0⦌ 0).op) x
  change f.app (Opposite.op ⦋1⦌) (PinchedHom.constant x 1) =
    PinchedHom.constant (f.app (Opposite.op ⦋0⦌) x) 1 at h
  change IsInvertibleEdge (edgeOfSimplex (f.app _ (PinchedHom.constant x 1)))
  rw [h, pinchedConstant_one]
  apply (isInvertibleEdge_congr (e := edgeOfSimplex _)
    (f := SSet.Truncated.Edge.id (X := (truncation 2).obj X) (f.app _ x)) rfl).mpr
  change IsIso (SSet.Truncated.HomotopyCategory.homMk
    (SSet.Truncated.Edge.id (X := (truncation 2).obj X) (f.app (Opposite.op ⦋0⦌) x)))
  rw [SSet.Truncated.HomotopyCategory.homMk_id]
  infer_instance

end SerrePositivity.InfinityCategories.F2
