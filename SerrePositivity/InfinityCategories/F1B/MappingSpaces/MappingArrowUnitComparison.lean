module

public import SerrePositivity.InfinityCategories.F1B.MappingSpaces.MappingArrowInterval
public import SerrePositivity.InfinityCategories.F1B.MappingSpaces.MappingArrowUnitFormula
public import SerrePositivity.InfinityCategories.F1B.MappingSpaces.IntervalFamilyInvariance

/-!
概要：coherent 比較の各点の射を抽出した単位の標準比較と照合する。
方針：恒等矢印からの伸長の像の正方形を、定値端点で正規化する。
規約：比較の同値性を仮定せず、実際のホモトピーで照合する。
使われ方：B1 の自然な比較から指定単位の局所判定への接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
namespace MappingArrowComparison
variable {X Y : SSet.{u}} {F : X ⟶ Y} {G : Y ⟶ X}
variable (q : MappingArrowComparison F G)

/-- 概要：抽出した単位の x 成分を任意のパラメータ上の定値端点で表示する。
方針：元の単位の raw な代表を定値 x に沿って制限する。
規約：代表を選び直さない。使われ方：区間比較の合成公式の左因子。 -/
def intervalUnitHomotopy (A : SSet.{u}) (x : X _⦋0⦌) :
    SSet.Homotopy (SSet.const x : A ⟶ X)
      (SSet.const (G.app (Opposite.op ⦋0⦌) (F.app (Opposite.op ⦋0⦌) x))) where
  h := ((SSet.const x : A ⟶ X) ▷ (Δ[1] : SSet.{u})) ≫ q.unitHomotopy.h
  h₀ := by rw [SSet.ι₀_comp_assoc, q.unitHomotopy.h₀, Category.comp_id]; rfl
  h₁ := by rw [SSet.ι₁_comp_assoc, q.unitHomotopy.h₁, SSet.const_comp]; rfl
  rel := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro z
    exact False.elim z.1.property

/-- 概要：抽出単位の定値族の類はその x 成分の定値化。
方針：同じ一次単体の端点輸送と、評価と定値化の一般公式を使う。
規約：パラメータ A は任意。使われ方：標準単位比較との合成因子の同定。 -/
lemma intervalUnitHomotopy_hom (A : SSet.{u}) (x : X _⦋0⦌) :
    SSet.Truncated.HomotopyCategory.homMk
      (functorEdgeOfSimplicialHomotopy (q.intervalUnitHomotopy A x)) =
        constantFunctorHomMap A (qcatUnitComponent q.unitHom x) := by
  let i : A ⟶ X := SSet.const x
  let e := (functorEdgeOfSimplicialHomotopy q.unitHomotopy).map
    ((truncation 2).map ((pre i).app X))
  have ht := homMk_transport
    (congrArg functorVertex (SSet.const_comp x (𝟙 X)))
    (congrArg functorVertex (SSet.const_comp x (F ≫ G))) e
    (functorEdgeOfSimplicialHomotopy (q.intervalUnitHomotopy A x))
    (by
      change ((pre i).app X).app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (curry q.unitHomotopy.h)) =
          SSet.yonedaEquiv (curry (q.intervalUnitHomotopy A x).h)
      rw [← SSet.yonedaEquiv_comp]
      apply congrArg SSet.yonedaEquiv
      apply uncurry_injective
      rw [uncurry_pre_app, uncurry_curry, uncurry_curry]
      rfl)
  have hv := functorHomEvaluate_constantFunctorHomMap A q.unitHom x
  change _ = constantFunctorHomMap A (functorHomEvaluate q.unitHom x)
  rw [← hv]
  exact ht.symm

/-- 概要：coherent 比較の区間射は抽出単位の標準比較を任意の族で表す。
方針：伸長の像の正方形から合成関係を読み、定値端点の輸送を揃える。
規約：パラメータ A は quasicategory。各点の同値性は仮定しない。
使われ方：標準単位比較との実際のホモトピーの存在判定。 -/
lemma intervalMap_familyHom {A : SSet.{u}} [Quasicategory A]
    [Quasicategory X] [Quasicategory Y] (x : X _⦋0⦌) (y : Y _⦋0⦌)
    (f : A ⟶ intervalMappingSpace (F.app (Opposite.op ⦋0⦌) x) y) :
    intervalFamilyHom (f ≫ q.intervalMap x y) =
      constantUnitHomMap q.unitHom A x y (intervalFamilyHom f) := by
  let H := leftMappingIntervalHomotopy F x y f
  have hs := functorHom_comp_eq_of_square (q.intervalUnitHomotopy A x)
    (q.intervalHomotopy x y f)
    (intervalFamilyHomotopy (f ≫ intervalFunctorMap G (F.app (Opposite.op ⦋0⦌) x) y))
    (unitCommaHomotopySquare (q.prefixComparison (SSet.const x) (SSet.const y) H))
    (q.prefixSquare_bottom (SSet.const x) (SSet.const y) H)
    (by
      rw [q.prefixSquare_top]
      apply congrArg curry
      change (intervalFamilyHomotopy f).h ≫ G =
        (intervalFamilyHomotopy (f ≫ intervalFunctorMap G _ _)).h
      change ((β_ A (Δ[1] : SSet.{u})).hom ≫ intervalMappingUncurry f) ≫ G =
        (β_ A (Δ[1] : SSet.{u})).hom ≫ intervalMappingUncurry (f ≫ intervalFunctorMap G _ _)
      rw [intervalFunctorMap_uncurry, Category.assoc])
    (by rw [q.prefixSquare_left]; rfl)
    (by rw [q.prefixSquare_right]; rfl)
  rw [q.intervalUnitHomotopy_hom] at hs
  change _ ≫ intervalFamilyHom (f ≫ intervalFunctorMap G _ _) = _ at hs
  rw [intervalFunctorMap_familyHom] at hs
  have hr : intervalFamilyHom (f ≫ q.intervalMap x y) =
      SSet.Truncated.HomotopyCategory.homMk
        (functorEdgeOfSimplicialHomotopy (q.intervalHomotopy x y f)) := by
    apply congrArg SSet.Truncated.HomotopyCategory.homMk
    apply congrArg functorEdgeOfSimplicialHomotopy
    apply RelativeMorphism.Homotopy.ext
    exact q.intervalMap_family_h x y f
  rw [hr, constantUnitHomMap_formula]
  exact hs.symm

/-- 概要：coherent 比較の各点の射は抽出単位の標準比較に実際にホモトピック。
方針：区間写像空間全体をパラメータとし、h Fun の族の類の一致を使う。
規約：比較の同値性は不要。使われ方：各点の同値性を指定単位版に移す。 -/
lemma intervalMap_unitIntervalMap_homotopy [Quasicategory X] [Quasicategory Y]
    (x : X _⦋0⦌) (y : Y _⦋0⦌) :
    Nonempty (SSet.Homotopy (q.intervalMap x y) (unitIntervalMap q.unitHom x y)) := by
  apply intervalFamilyHom_eq_imp_homotopy
  have hq := q.intervalMap_familyHom x y (𝟙 _)
  have hu := unitIntervalMap_family q.unitHom x y (𝟙 _)
  simpa only [Category.id_comp] using hq.trans hu.symm

end MappingArrowComparison
end SerrePositivity.InfinityCategories
