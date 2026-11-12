module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.PinchedUniversal

/-!
概要：端点の等式による pinched 写像空間の同型と展開した族の不変性。
方針：端点の等式を消去し、恒等同型に戻して比較する。
規約：端点の等式は新たな射やホモトピーの選択を含まない。
使われ方：写像空間の引き戻しで底の二つの端点表示を揃える。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：等しい端点を持つ pinched 写像空間は厳密に同型。
方針：端点に関する型の等式の同型を使う。
規約：単体の値を保つ同型。
使われ方：引き戻しの底の写像空間の端点の正規化。 -/
def pinchedHomTransportIso {X : SSet.{u}} {x y x' y' : X _⦋0⦌}
    (hx : x = x') (hy : y = y') : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x y ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x' y' :=
  eqToIso (congrArg₂ (fun a b ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom a b) hx hy)

/-- 概要：端点の等式による同型は各単体の値を保つ。
方針：二つの等式を消去する。
規約：全次数で成立する。
使われ方：引き戻し四角形の可換性の照合。 -/
lemma pinchedHomTransportIso_hom_val {X : SSet.{u}} {x y x' y' : X _⦋0⦌}
    (hx : x = x') (hy : y = y') (n : ℕ) (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x y) _⦋n⦌) :
    ((pinchedHomTransportIso hx hy).hom.app (Opposite.op ⦋n⦌) s).val = s.val := by
  cases hx
  cases hy
  rfl

/-- 概要：端点の等式による同型は展開した pinched 族を保つ。
方針：等式を消去し、恒等射との合成を消す。
規約：パラメータの単体集合は任意。
使われ方：写像空間の引き戻しの族を元の空間へ持ち上げる。 -/
lemma pinchedHomTransportIso_uncurry {A X : SSet.{u}} {x y x' y' : X _⦋0⦌}
    (hx : x = x') (hy : y = y') (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomUncurry (f ≫ (pinchedHomTransportIso hx hy).hom) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomUncurry f := by
  cases hx
  cases hy
  simp only [pinchedHomTransportIso, eqToIso_refl, Iso.refl_hom, Category.comp_id]

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
