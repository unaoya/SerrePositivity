module
public import SerrePositivity.InfinityCategories.DoldKanComparison.CoherentPinchedStandard
public import SerrePositivity.InfinityCategories.DoldKanComparison.StandardComposition

/-! # 実 dg pinched Hom の全次元合成

概要：標準 DK Hom の AW 合成を実 pinched Hom へ移し、有限族にも適用する。
方針：標準 Hom と実 Hom の単体的同型で合成写像を共役する。
規約：第一因子が前の射、第二因子が後の射。高次三角形との比較は別に必要。
使われ方：共通実 Ore 細分から合成分子の族を作る。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v t
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory CartesianMonoidalCategory DifferentialGraded DoldKanComparison
open scoped Simplicial

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

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 標準 AW 合成を移した、実 dg pinched Hom の全次元合成。 -/
def pinchedHomComposition (x y z : D) :
    DGNerve.pinchedHom A D x y ⊗ DGNerve.pinchedHom A D y z ⟶
      DGNerve.pinchedHom A D x z :=
  ((standardHomPinchedIso x y).inv ⊗ₘ (standardHomPinchedIso y z).inv) ≫
    pinchedUliftHomPair _ _ ≫ SSet.uliftFunctor.map (standardComposition x y z) ≫
      (standardHomPinchedIso x z).hom

/-- 合成の実単体は、同じ標準座標の AW 合成そのもの。 -/
lemma pinchedHomComposition_app (x y z : D) {n : ℕ}
    (f : (DGNerve.pinchedHom A D x y) _⦋n⦌)
    (g : (DGNerve.pinchedHom A D y z) _⦋n⦌) :
    (pinchedHomComposition x y z).app _ (f, g) =
      (standardHomPinchedIso x z).hom.app _ (ULift.up
        (standardAW ((standardHomPinchedIso y z).inv.app _ g).down
          ((standardHomPinchedIso x y).inv.app _ f).down)) := rfl

/-- 実合成を標準座標へ戻すと、指定二単体の AW 合成になる。 -/
lemma pinchedHomComposition_standard (x y z : D) {n : ℕ}
    (f : (DGNerve.pinchedHom A D x y) _⦋n⦌)
    (g : (DGNerve.pinchedHom A D y z) _⦋n⦌) :
    ((standardHomPinchedIso x z).inv.app _
      ((pinchedHomComposition x y z).app _ (f, g))).down =
        standardAW ((standardHomPinchedIso y z).inv.app _ g).down
          ((standardHomPinchedIso x y).inv.app _ f).down := by
  rw [pinchedHomComposition_app]
  exact congrArg ULift.down (ConcreteCategory.congr_hom
    (NatTrans.congr_app (standardHomPinchedIso x z).hom_inv_id (Opposite.op ⦋n⦌)) _)

/-- 同じ次数の実 pinched 単体の合成は厳密な結合律を持つ。 -/
lemma pinchedHomComposition_assoc (w x y z : D) {n : ℕ}
    (f : (DGNerve.pinchedHom A D w x) _⦋n⦌)
    (g : (DGNerve.pinchedHom A D x y) _⦋n⦌)
    (h : (DGNerve.pinchedHom A D y z) _⦋n⦌) :
    (pinchedHomComposition w y z).app _ ((pinchedHomComposition w x y).app _ (f, g), h) =
      (pinchedHomComposition w x z).app _ (f, (pinchedHomComposition x y z).app _ (g, h)) := by
  rw [pinchedHomComposition_app w y z, pinchedHomComposition_app w x z,
    pinchedHomComposition_standard w x y, pinchedHomComposition_standard x y z,
    standardAW_assoc]

/-- 標準 DK 単位を移した、全次数の実 pinched 単位単体。 -/
def pinchedHomUnitSimplex (x : D) (n : ℕ) : (DGNerve.pinchedHom A D x x) _⦋n⦌ :=
  (standardHomPinchedIso x x).hom.app _ (ULift.up (standardUnit x n))

/-- 実 pinched 単位単体の標準座標は、同じ次数の標準単位。 -/
lemma pinchedHomUnitSimplex_standard (x : D) (n : ℕ) :
    ((standardHomPinchedIso x x).inv.app _ (pinchedHomUnitSimplex x n)).down =
      standardUnit (R := A) x n :=
  congrArg ULift.down (ConcreteCategory.congr_hom
    (NatTrans.congr_app (standardHomPinchedIso x x).hom_inv_id (Opposite.op ⦋n⦌)) _)

/-- 実 pinched 合成の左単位則は全次元で厳密に成立する。 -/
lemma pinchedHomComposition_unit_left (x y : D) {n : ℕ}
    (f : (DGNerve.pinchedHom A D x y) _⦋n⦌) :
    (pinchedHomComposition x y y).app _ (f, pinchedHomUnitSimplex y n) = f := by
  rw [pinchedHomComposition_app, pinchedHomUnitSimplex_standard, standardAW_unit_left]
  have hi := pinchedIso_inv_hom_apply (standardHomPinchedIso x y) f
  simpa only [ULift.up_down] using hi

/-- 実 pinched 合成の右単位則は全次元で厳密に成立する。 -/
lemma pinchedHomComposition_unit_right (x y : D) {n : ℕ}
    (f : (DGNerve.pinchedHom A D x y) _⦋n⦌) :
    (pinchedHomComposition x x y).app _ (pinchedHomUnitSimplex x n, f) = f := by
  rw [pinchedHomComposition_app, pinchedHomUnitSimplex_standard, standardAW_unit_right]
  have hi := pinchedIso_inv_hom_apply (standardHomPinchedIso x y) f
  simpa only [ULift.up_down] using hi

/-- 同じ単体集合でパラメータ付けられた二分子族の合成。 -/
def pinchedHomCompositionFamily {K : SSet.{max u v}} {x y z : D}
    (f : K ⟶ DGNerve.pinchedHom A D x y) (g : K ⟶ DGNerve.pinchedHom A D y z) :
    K ⟶ DGNerve.pinchedHom A D x z :=
  CartesianMonoidalCategory.lift f g ≫ pinchedHomComposition x y z

/-- 合成族は任意のパラメータ射の前合成と厳密に可換する。 -/
lemma pinchedHomCompositionFamily_precomp {K L : SSet.{max u v}} {x y z : D}
    (f : K ⟶ DGNerve.pinchedHom A D x y) (g : K ⟶ DGNerve.pinchedHom A D y z)
    (i : L ⟶ K) :
    i ≫ pinchedHomCompositionFamily f g = pinchedHomCompositionFamily (i ≫ f) (i ≫ g) := by
  simp only [pinchedHomCompositionFamily, ← Category.assoc,
    CartesianMonoidalCategory.comp_lift]

/-- 三つの全パラメータ族の合成は、族全体で厳密に結合的。 -/
lemma pinchedHomCompositionFamily_assoc {K : SSet.{max u v}} {w x y z : D}
    (f : K ⟶ DGNerve.pinchedHom A D w x) (g : K ⟶ DGNerve.pinchedHom A D x y)
    (h : K ⟶ DGNerve.pinchedHom A D y z) :
    pinchedHomCompositionFamily (pinchedHomCompositionFamily f g) h =
      pinchedHomCompositionFamily f (pinchedHomCompositionFamily g h) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro k
  exact pinchedHomComposition_assoc w x y z (f.app n k) (g.app n k) (h.app n k)

end SerrePositivity.InfinityCategories
