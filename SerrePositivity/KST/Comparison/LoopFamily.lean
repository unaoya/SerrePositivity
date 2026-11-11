module

public import SerrePositivity.KST.Spectra.SuspensionLoop
public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy
public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary

/-!
# 基点ループの族を円の商へ降ろす

概要：区間の両端が基点となる単体的族を円の商の普遍性へ渡す。
方針：区間の族を curry し、境界の二つの面で基点への一致を確認する。
規約：Segal 1974 Proposition 1.5 の M→ΩBM の随伴。ループ対象は K-L9 のものを借りる。
使われ方：群完備化の標準写像の構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonoidalClosed
open BraidedCategory
open scoped Simplicial

/--
概要：点付き単体集合の基点への定数写像を終対象経由で表す。
方針：終対象からの射と頂点の同値の逆合成を使う。
規約：Segal 1974 Proposition 1.5 の基点の規約。
使われ方：円の商の普遍性の定数写像との照合。
-/
theorem const_basepoint (X : SSet.{u}) (Y : PointedSimplicialSet.{u}) :
    SSet.const (X := X) (PointedSimplicialSet.basepoint Y) = toUnit X ≫ Y.hom := by
  calc
    _ = toUnit X ≫ (SSet.unitHomEquiv Y.right).symm (PointedSimplicialSet.basepoint Y) := rfl
    _ = toUnit X ≫ Y.hom := congrArg (fun k => toUnit X ≫ k)
      ((SSet.unitHomEquiv Y.right).symm_apply_apply Y.hom)

/--
概要：内部 Hom の全てのパラメータで基点を値とする点を選ぶ。
方針：終対象経由の定数写像を curry する。
規約：Segal 1974 Proposition 1.5 のループ族のパラメータ。
使われ方：円からパラメータ付き写像空間への点付き射。
-/
def parameterMappingPointed (X : SSet.{u})
    (Y : PointedSimplicialSet.{u}) : PointedSimplicialSet.{u} :=
  Under.mk (curry (toUnit (X ⊗ 𝟙_ SSet.{u}) ≫ Y.hom))

/--
概要：基点ループの族を curry すると区間の境界は内部 Hom の基点へ送られる。
方針：境界の二面で比較し、それぞれ元のホモトピーの端点条件を使う。
規約：Segal 1974 Proposition 1.5 の円への因子化の条件。
使われ方：単体的円の商の普遍性。
-/
theorem loopFamily_boundary_map {X : SSet.{u}} (Y : PointedSimplicialSet.{u})
    (h : X ⊗ (Δ[1] : SSet.{u}) ⟶ Y.right)
    (h₀ : SSet.ι₀ ≫ h = SSet.const (PointedSimplicialSet.basepoint Y))
    (h₁ : SSet.ι₁ ≫ h = SSet.const (PointedSimplicialSet.basepoint Y)) :
    (SSet.boundary.{u} 1).ι ≫ curry h = toUnit _ ≫ (parameterMappingPointed X Y).hom := by
  apply SSet.boundary.hom_ext
  intro i
  rw [← Category.assoc, SSet.boundary.ι_ι]
  change SSet.stdSimplex.δ i ≫ curry h =
    SSet.boundary.ι i ≫ toUnit _ ≫ curry (toUnit (X ⊗ 𝟙_ SSet.{u}) ≫ Y.hom)
  rw [comp_toUnit_assoc, ← PointedObject.curry_constant, ← curry_natural_left]
  congr 1
  fin_cases i
  · change X ◁ (SSet.stdSimplex.δ (0 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1]) ≫ h = _
    rw [SSet.stdSimplex.δ_zero_eq_const.{u}]
    change (fst X (Δ[0] : SSet.{u}) ≫ SSet.ι₁) ≫ h = _
    rw [Category.assoc, h₁, const_basepoint]
    simp only [comp_toUnit_assoc]
  · change X ◁ (SSet.stdSimplex.δ (1 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1]) ≫ h = _
    rw [SSet.stdSimplex.δ_one_eq_const.{u}]
    change (fst X (Δ[0] : SSet.{u}) ≫ SSet.ι₀) ≫ h = _
    rw [Category.assoc, h₀, const_basepoint]
    simp only [comp_toUnit_assoc]

/--
概要：基点ループの実ホモトピーは円の商の境界条件を満たす。
方針：区間写像と二つの端点の証明を取り出す。
規約：Segal 1974 Proposition 1.5 の標準写像。
使われ方：円への点付き因子化。
-/
theorem loopFamily_boundary {X : SSet.{u}} (Y : PointedSimplicialSet.{u})
    (H : SSet.Homotopy (SSet.const (X := X) (PointedSimplicialSet.basepoint Y))
      (SSet.const (PointedSimplicialSet.basepoint Y))) :
    (SSet.boundary.{u} 1).ι ≫ curry H.h = toUnit _ ≫ (parameterMappingPointed X Y).hom :=
  loopFamily_boundary_map Y H.h H.h₀ H.h₁

/--
概要：基点ループの族を円から内部 Hom への点付き射へ降ろす。
方針：区間の境界が基点に潰れることを cofiber の普遍性へ入力する。
規約：Segal 1974 Proposition 1.5。実際の単体的円 Δ¹/∂Δ¹ を使う。
使われ方：ループ空間への標準写像の構成。
-/
def loopFamilyCircle {X : SSet.{u}} (Y : PointedSimplicialSet.{u})
    (H : SSet.Homotopy (SSet.const (X := X) (PointedSimplicialSet.basepoint Y))
      (SSet.const (PointedSimplicialSet.basepoint Y))) :
    PointedSimplicialSet.circle ⟶ parameterMappingPointed X Y :=
  PointedObject.cofiberDesc (SSet.boundary.{u} 1).ι (parameterMappingPointed X Y)
    (curry H.h) (loopFamily_boundary Y H)
/--
概要：点付き写像のパラメータと定義域を交換し、点付き内部 Hom への射を作る。
方針：評価を対称性で交換して curry し、基点条件で等化子へ持ち上げる。
規約：Segal 1974 Proposition 1.5 のループ族の随伴。内部 Hom は K-L9 と共通。
使われ方：円からのパラメータ付き写像をループ空間への射にする。
-/
def parameterMappingTranspose {X : SSet.{u}} {Y K : PointedSimplicialSet.{u}}
    (f : K ⟶ parameterMappingPointed X Y) : X ⟶ (PointedObject.basedHom K Y).right := by
  let g := (β_ K.right X).hom ≫ uncurry f.right
  have hc : K.hom ▷ X ≫ g = toUnit ((𝟙_ SSet.{u}) ⊗ X) ≫ Y.hom := by
    dsimp only [g]
    rw [← Category.assoc, braiding_naturality_left, Category.assoc,
      ← uncurry_natural_left, Under.w f]
    change (β_ (𝟙_ SSet.{u}) X).hom ≫
      uncurry (curry (toUnit (X ⊗ 𝟙_ SSet.{u}) ≫ Y.hom)) = _
    rw [uncurry_curry]
    simp only [comp_toUnit_assoc]
  exact equalizer.lift (f := PointedObject.homRestriction K Y)
    (g := PointedObject.homConstant K Y) (curry g) (by
      rw [PointedObject.homRestriction, curry_pre_app, hc, PointedObject.curry_constant]
      simp only [PointedObject.homConstant, PointedObject.homBasepoint, PointedObject.point,
        comp_toUnit_assoc]
      rfl)

/--
概要：転置した写像を基礎指数へ含めると通常の curry である。
方針：等化子への持ち上げの計算則を使う。
規約：Segal 1974 Proposition 1.5 の写像の具体的な同定。
使われ方：標準ループ族を評価で復元する。
-/
@[reassoc] theorem parameterMappingTranspose_ι {X : SSet.{u}}
    {Y K : PointedSimplicialSet.{u}} (f : K ⟶ parameterMappingPointed X Y) :
    parameterMappingTranspose f ≫ PointedObject.basedHomι K Y =
      curry ((β_ K.right X).hom ≫ uncurry f.right) := equalizer.lift_ι ..

/--
概要：基点ループの実単体的族から K-L9 のループ空間への射を構成する。
方針：区間の境界を潰して円へ降ろし、パラメータを転置する。
規約：Segal 1974 Proposition 1.5 の標準写像。比較同値性は別の定理。
使われ方：群完備化写像の実際の終域。
-/
def loopFamilyMap {X : SSet.{u}} (Y : PointedSimplicialSet.{u})
    (H : SSet.Homotopy (SSet.const (X := X) (PointedSimplicialSet.basepoint Y))
      (SSet.const (PointedSimplicialSet.basepoint Y))) : X ⟶ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).right :=
  parameterMappingTranspose (loopFamilyCircle Y H)

/--
概要：円の商からの写像を区間へ引き戻して評価すると元のループ族に戻る。
方針：転置と curry の計算則、対称性の自然性、商の普遍性の計算則を使う。
規約：Segal 1974 Proposition 1.5 の標準写像との一致。
使われ方：群完備化写像が任意の選択ではなく標準ループ族を表すことの保証。
-/
theorem loopFamilyMap_evaluation {X : SSet.{u}} (Y : PointedSimplicialSet.{u})
    (H : SSet.Homotopy (SSet.const (X := X) (PointedSimplicialSet.basepoint Y))
      (SSet.const (PointedSimplicialSet.basepoint Y))) :
    PointedObject.cofiberQuotient (SSet.boundary.{u} 1).ι ▷ X ≫
      uncurry (loopFamilyMap Y H ≫ PointedObject.basedHomι PointedSimplicialSet.circle Y) =
        (β_ (Δ[1] : SSet.{u}) X).hom ≫ H.h := by
  rw [loopFamilyMap, parameterMappingTranspose_ι, uncurry_curry]
  dsimp only [loopFamilyCircle, PointedSimplicialSet.circle, PointedSimplicialSet.sphere]
  rw [← Category.assoc, braiding_naturality_left, Category.assoc, ← uncurry_natural_left,
    PointedObject.cofiberQuotient_desc, uncurry_curry]


end SerrePositivity.KST.Comparison
