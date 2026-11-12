module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpaceKan

/-!
概要：右 pinched 写像空間の単体集合の射への関手性。
方針：各単体に後合成し、始点と終点の固定条件を自然性で移す。
規約：PinchedHom レーンの定義は変更しない。
使われ方：HTT §2.2、Kerodon §4.8.3（Tag 05AW） の充満忠実性。

対応節は Kerodon 4.8（Tag 0578）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors

/-- 概要：定値単体の像は像の頂点の定値単体。
方針：零単体への射に対する自然性を使う。
規約：全次数で成立する。
使われ方：Kerodon §4.8.3（Tag 05AW） の pinched 写像空間への作用。 -/
lemma pinchedConstant_map {X Y : SSet.{u}} (f : X ⟶ Y) (x : X _⦋0⦌) (n : ℕ) :
    f.app (Opposite.op ⦋n⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x n) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (f.app (Opposite.op ⦋0⦌) x) n :=
  ConcreteCategory.congr_hom (f.naturality (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0).op) x

/-- 概要：右 pinched 単体を単体集合の射で写す。
方針：元の単体の像に自然性から得る固定条件を付ける。
規約：両端も f で写す。
使われ方：Kerodon §4.8.3（Tag 05AW） の写像空間の射。 -/
def pinchedSimplexMap {X Y : SSet.{u}} (f : X ⟶ Y) {x y : X _⦋0⦌} {n : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.Simplex x y n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.Simplex (f.app (Opposite.op ⦋0⦌) x) (f.app (Opposite.op ⦋0⦌) y) n where
  val := f.app (Opposite.op ⦋n + 1⦌) s.val
  source := by
    calc
      _ = f.app (Opposite.op ⦋n⦌) (X.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.front n).op s.val) :=
        (ConcreteCategory.congr_hom (f.naturality (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.front n).op) s.val).symm
      _ = _ := by rw [s.source, pinchedConstant_map]
  target := by
    calc
      _ = f.app (Opposite.op ⦋0⦌) (X.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.lastVertex n).op s.val) :=
        (ConcreteCategory.congr_hom (f.naturality (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.lastVertex n).op) s.val).symm
      _ = _ := by rw [s.target]

/-- 概要：単体集合の射は右 pinched 写像空間の射を誘導する。
方針：各次数の単体の像を取り、終点固定延長への自然性を確認する。
規約：quasicategory 性は定義に不要。
使われ方：HTT §2.2、Kerodon §4.8.3（Tag 05AW） の充満忠実性。 -/
def pinchedHomMap {X Y : SSet.{u}} (f : X ⟶ Y) (x y : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x y ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (f.app (Opposite.op ⦋0⦌) x) (f.app (Opposite.op ⦋0⦌) y) where
  app _ := ↾pinchedSimplexMap f
  naturality {d e} α := by
    apply ConcreteCategory.hom_ext
    intro s
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.Simplex.ext
    exact ConcreteCategory.congr_hom (f.naturality (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extend α.unop).op) s.val

/-- 概要：恒等射は写像空間の恒等射を誘導する。
方針：元の単体への作用を比較する。
規約：両端は固定。
使われ方：Kerodon §4.8.3（Tag 05AW） の関手法則。 -/
lemma pinchedHomMap_id {X : SSet.{u}} (x y : X _⦋0⦌) : pinchedHomMap (𝟙 X) x y = 𝟙 _ := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro s
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.Simplex.ext
  rfl

/-- 概要：合成射の写像空間への作用は作用の合成。
方針：元の単体の像を比較する。
規約：f の後で g を適用する。
使われ方：Kerodon §4.8.3（Tag 05AW） の関手法則。 -/
lemma pinchedHomMap_comp {X Y Z : SSet.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x y : X _⦋0⦌) :
    pinchedHomMap (f ≫ g) x y = pinchedHomMap f x y ≫
      pinchedHomMap g (f.app (Opposite.op ⦋0⦌) x) (f.app (Opposite.op ⦋0⦌) y) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro s
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.Simplex.ext
  rfl

/-- 概要：写像空間の π₀ とホモトピー圏の Hom の比較は射に自然。
方針：零単体の代表へ帰着し、辺の類の自然性を使う。
規約：この自然性は quasicategory 性を仮定しない写像で主張する。
使われ方：Kerodon §4.8.3（Tag 05AW） の充満忠実性とホモトピー圏の比較。 -/
lemma pinchedHomPiZeroToHom_naturality {X Y : SSet.{u}} (f : X ⟶ Y) (x y : X _⦋0⦌)
    (a : SSet.π₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x y)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomPiZeroToHom (f.app (Opposite.op ⦋0⦌) x) (f.app (Opposite.op ⦋0⦌) y)
      (SSet.mapπ₀ (pinchedHomMap f x y) a) =
        (hoFunctor.map f).toFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomPiZeroToHom x y a) := by
  obtain ⟨s, rfl⟩ := SSet.π₀.mk_surjective a
  rfl

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors
