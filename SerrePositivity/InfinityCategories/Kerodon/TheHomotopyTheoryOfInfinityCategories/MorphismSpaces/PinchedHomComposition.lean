module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CoherentPinchedStandard
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardComposition

/-! # 実 dg pinched Hom の全次元合成

概要：標準 DK Hom の AW 合成を実 pinched Hom へ移し、有限族にも適用する。
方針：標準 Hom と実 Hom の単体的同型で合成写像を共役する。
規約：第一因子が前の射、第二因子が後の射。高次三角形との比較は別に必要。
使われ方：共通実 Ore 細分から合成分子の族を作る。

対応節は Kerodon 4.6（Tag 01J3）。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v t
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open CategoryTheory MonoidalCategory CartesianMonoidalCategory DifferentialGraded
open scoped _root_.Simplicial

/-- 宇宙持ち上げと実単体ごとの積を結ぶ標準写像。 -/
def pinchedUliftHomPair (X Y : SSet.{u}) :
    SSet.uliftFunctor.{v, u}.obj X ⊗ SSet.uliftFunctor.{v, u}.obj Y ⟶
      SSet.uliftFunctor.{v, u}.obj (X ⊗ Y) where
  app _ := ↾fun p => ULift.up (p.1.down, p.2.down)
  naturality _ _ _ := rfl

/-- 単体的同型の逆から戻す等式を、同型の内部構成を展開せず適用する。 -/
lemma pinchedIso_inv_hom_apply {X Y : SSet.{t}} (e : X ≅ Y) {n : ℕ}
    (f : Y _⦋n⦌) : e.hom.app _ (e.inv.app _ f) = f :=
  ConcreteCategory.congr_hom (NatTrans.congr_app e.inv_hom_id (Opposite.op ⦋n⦌)) f

variable {A : Type u} [CommRing A] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]

/-- 標準 AW 合成を移した、実 dg pinched Hom の全次元合成。 -/
def pinchedHomComposition (x y z : D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D y z ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x z :=
  ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomPinchedIso x y).inv ⊗ₘ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomPinchedIso y z).inv) ≫
    pinchedUliftHomPair _ _ ≫ SSet.uliftFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardComposition x y z) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomPinchedIso x z).hom

/-- 合成の実単体は、同じ標準座標の AW 合成そのもの。 -/
lemma pinchedHomComposition_app (x y z : D) {n : ℕ}
    (f : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y) _⦋n⦌)
    (g : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D y z) _⦋n⦌) :
    (pinchedHomComposition x y z).app _ (f, g) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomPinchedIso x z).hom.app _ (ULift.up
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardAW ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomPinchedIso y z).inv.app _ g).down
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomPinchedIso x y).inv.app _ f).down)) := rfl

/-- 実合成を標準座標へ戻すと、指定二単体の AW 合成になる。 -/
lemma pinchedHomComposition_standard (x y z : D) {n : ℕ}
    (f : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y) _⦋n⦌)
    (g : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D y z) _⦋n⦌) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomPinchedIso x z).inv.app _
      ((pinchedHomComposition x y z).app _ (f, g))).down =
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardAW ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomPinchedIso y z).inv.app _ g).down
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomPinchedIso x y).inv.app _ f).down := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomComposition_app]
  exact congrArg ULift.down (ConcreteCategory.congr_hom
    (NatTrans.congr_app (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomPinchedIso x z).hom_inv_id (Opposite.op ⦋n⦌)) _)

/-- 同じ次数の実 pinched 単体の合成は厳密な結合律を持つ。 -/
lemma pinchedHomComposition_assoc (w x y z : D) {n : ℕ}
    (f : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D w x) _⦋n⦌)
    (g : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y) _⦋n⦌)
    (h : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D y z) _⦋n⦌) :
    (pinchedHomComposition w y z).app _ ((pinchedHomComposition w x y).app _ (f, g), h) =
      (pinchedHomComposition w x z).app _ (f, (pinchedHomComposition x y z).app _ (g, h)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomComposition_app w y z, pinchedHomComposition_app w x z,
    pinchedHomComposition_standard w x y, pinchedHomComposition_standard x y z,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardAW_assoc]

/-- 標準 DK 単位を移した、全次数の実 pinched 単位単体。 -/
def pinchedHomUnitSimplex (x : D) (n : ℕ) : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x x) _⦋n⦌ :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomPinchedIso x x).hom.app _ (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardUnit x n))

/-- 実 pinched 単位単体の標準座標は、同じ次数の標準単位。 -/
lemma pinchedHomUnitSimplex_standard (x : D) (n : ℕ) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomPinchedIso x x).inv.app _ (pinchedHomUnitSimplex x n)).down =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardUnit (R := A) x n :=
  congrArg ULift.down (ConcreteCategory.congr_hom
    (NatTrans.congr_app (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomPinchedIso x x).hom_inv_id (Opposite.op ⦋n⦌)) _)

/-- 実 pinched 合成の左単位則は全次元で厳密に成立する。 -/
lemma pinchedHomComposition_unit_left (x y : D) {n : ℕ}
    (f : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y) _⦋n⦌) :
    (pinchedHomComposition x y y).app _ (f, pinchedHomUnitSimplex y n) = f := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomComposition_app, pinchedHomUnitSimplex_standard, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardAW_unit_left]
  have hi := pinchedIso_inv_hom_apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomPinchedIso x y) f
  simpa only [ULift.up_down] using hi

/-- 実 pinched 合成の右単位則は全次元で厳密に成立する。 -/
lemma pinchedHomComposition_unit_right (x y : D) {n : ℕ}
    (f : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y) _⦋n⦌) :
    (pinchedHomComposition x x y).app _ (pinchedHomUnitSimplex x n, f) = f := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomComposition_app, pinchedHomUnitSimplex_standard, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardAW_unit_right]
  have hi := pinchedIso_inv_hom_apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomPinchedIso x y) f
  simpa only [ULift.up_down] using hi

/-- 同じ単体集合でパラメータ付けられた二分子族の合成。 -/
def pinchedHomCompositionFamily {K : SSet.{max u v}} {x y z : D}
    (f : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y) (g : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D y z) :
    K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x z :=
  CartesianMonoidalCategory.lift f g ≫ pinchedHomComposition x y z

/-- 合成族は任意のパラメータ射の前合成と厳密に可換する。 -/
lemma pinchedHomCompositionFamily_precomp {K L : SSet.{max u v}} {x y z : D}
    (f : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y) (g : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D y z)
    (i : L ⟶ K) :
    i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomCompositionFamily f g = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomCompositionFamily (i ≫ f) (i ≫ g) := by
  simp only [pinchedHomCompositionFamily, ← Category.assoc,
    CartesianMonoidalCategory.comp_lift]

/-- 三つの全パラメータ族の合成は、族全体で厳密に結合的。 -/
lemma pinchedHomCompositionFamily_assoc {K : SSet.{max u v}} {w x y z : D}
    (f : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D w x) (g : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y)
    (h : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D y z) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomCompositionFamily (pinchedHomCompositionFamily f g) h =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomCompositionFamily f (pinchedHomCompositionFamily g h) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro k
  exact pinchedHomComposition_assoc w x y z (f.app n k) (g.app n k) (h.app n k)

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
