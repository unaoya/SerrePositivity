module
public import SerrePositivity.InfinityCategories.DGNerve.PinchedModule

/-! # 右 pinched 写像空間の単体的加群

概要：実際の右 pinched 写像空間を ModuleCat A に値を持つ単体的対象にまとめる。
方針：各次数の移送した加群と、元の引き戻しに一致する線形写像を使う。
規約：HA Construction 1.3.1.6、Kerodon §4.6.5。使われ方：単体的 A 加群としての写像空間。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.DGNerve.PinchedHom

open CategoryTheory DifferentialGraded Opposite
open scoped Simplicial

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：実際の右 pinched 写像空間は単体的 A 加群となる。
方針：各次元をその加群として取り、引き戻しの線形写像と恒等・合成則を使う。
規約：Kerodon §4.6.5。使われ方：写像空間の線形な単体的構造。 -/
def moduleObject (x y : D) : SimplicialObject (ModuleCat.{max u v} A) where
  obj n := ModuleCat.of A (InfinityCategories.PinchedHom.Simplex (X := dgNerve A D)
    (Simplex.vertex x) (Simplex.vertex y) n.unop.len)
  map f := ModuleCat.ofHom (pullbackLinear (x := x) (y := y) f.unop)
  map_id n := by
    ext s
    change pullbackLinear (𝟙 n.unop) s = s
    rw [pullbackLinear_apply]
    exact s.pullback_id
  map_comp f g := by
    ext s
    change pullbackLinear (g.unop ≫ f.unop) s =
      pullbackLinear g.unop (pullbackLinear f.unop s)
    rw [pullbackLinear_apply, pullbackLinear_apply, pullbackLinear_apply]
    exact (s.pullback_comp g.unop f.unop).symm

/-- 概要：単体的加群の写像の値は元の単体的集合の写像。
方針：各写像に使った線形引き戻しの値を計算する。
規約：Kerodon §4.6.5。使われ方：元の写像空間の構造を保った線形性の利用。 -/
lemma moduleObject_map_apply (x y : D) {m n : SimplexCategoryᵒᵖ} (f : m ⟶ n)
    (s : (DGNerve.pinchedHom A D x y).obj m) :
    (moduleObject (A := A) x y).map f s = (DGNerve.pinchedHom A D x y).map f s :=
  pullbackLinear_apply f.unop s

end SerrePositivity.InfinityCategories.DGNerve.PinchedHom
