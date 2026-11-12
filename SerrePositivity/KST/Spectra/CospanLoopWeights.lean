module

public import SerrePositivity.KST.Spectra.FreeInterval
public import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Cospan

/-!
概要：loop の区間重みと二辺のホーンの重みを、同じ二単体の重みで比較する。
方針：両端は同じ標準零単体に固定し、中央だけを区間・ホーン・二単体へ変える。
規約：全て実際の cospan 図式と自然変換。使われ方：基点付き loop の Hom–end 表示。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra

/-- 両端を標準区間の始点・終点へ送る、loop の区間重み。 -/
def loopIntervalWeight : AsSmall.{u} WalkingCospan ⥤ SSet.{u} :=
  AsSmall.down ⋙ cospan (stdSimplex.δ (1 : Fin 2)) (stdSimplex.δ (0 : Fin 2))

/-- 二単体の最初の二頂点に両端を置く、共通の比較重み。 -/
def loopTriangleWeight : AsSmall.{u} WalkingCospan ⥤ SSet.{u} :=
  AsSmall.down ⋙ cospan (stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (2 : Fin 3))
    (stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (2 : Fin 3))

/-- 二辺のホーンの外側の二頂点に両端を置く重み。 -/
def loopHornWeight : AsSmall.{u} WalkingCospan ⥤ SSet.{u} :=
  AsSmall.down ⋙ cospan (stdSimplex.δ (1 : Fin 2) ≫ horn₂₂.ι₀₂)
    (stdSimplex.δ (1 : Fin 2) ≫ horn₂₂.ι₁₂)

/-- 区間を二単体の 0–1 辺へ含める、両端固定の自然変換。 -/
def loopIntervalToTriangle : loopIntervalWeight.{u} ⟶ loopTriangleWeight :=
  Functor.whiskerLeft AsSmall.down (cospanHomMk (stdSimplex.δ (2 : Fin 3))
    (𝟙 _) (𝟙 _) (by simp) (by simp))

/-- ホーンを二単体へ含める、両端固定の自然変換。 -/
def loopHornToTriangle : loopHornWeight.{u} ⟶ loopTriangleWeight :=
  Functor.whiskerLeft AsSmall.down (cospanHomMk (horn 2 2).ι (𝟙 _) (𝟙 _)
    (by
      change (stdSimplex.δ (1 : Fin 2) ≫ horn₂₂.ι₀₂) ≫ (horn 2 2).ι =
        𝟙 (Δ[0] : SSet.{u}) ≫ (stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (2 : Fin 3))
      simp only [Category.id_comp, Category.assoc, horn.ι_ι]
      apply SSet.yonedaEquiv.injective
      decide)
    (by
      change (stdSimplex.δ (1 : Fin 2) ≫ horn₂₂.ι₁₂) ≫ (horn 2 2).ι =
        𝟙 (Δ[0] : SSet.{u}) ≫ (stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (2 : Fin 3))
      simp only [Category.id_comp, Category.assoc, horn.ι_ι]
      apply SSet.yonedaEquiv.injective
      decide))

/-- 第三頂点を第二頂点へ潰す、共通重みから区間重みへの射影。 -/
def loopTriangleToInterval : loopTriangleWeight.{u} ⟶ loopIntervalWeight :=
  Functor.whiskerLeft AsSmall.down (cospanHomMk (stdSimplex.σ (1 : Fin 2)) (𝟙 _) (𝟙 _)
    (by
      change (stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (2 : Fin 3)) ≫
        stdSimplex.σ (1 : Fin 2) = 𝟙 (Δ[0] : SSet.{u}) ≫ stdSimplex.δ (1 : Fin 2)
      rw [Category.id_comp]
      apply SSet.yonedaEquiv.injective
      decide)
    (by
      change (stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (2 : Fin 3)) ≫
        stdSimplex.σ (1 : Fin 2) = 𝟙 (Δ[0] : SSet.{u}) ≫ stdSimplex.δ (0 : Fin 2)
      rw [Category.id_comp]
      apply SSet.yonedaEquiv.injective
      decide))

/-- 区間の包含に続く射影は、両端を含む図式全体で恒等。 -/
lemma loopIntervalToTriangle_projection :
    loopIntervalToTriangle.{u} ≫ loopTriangleToInterval = 𝟙 loopIntervalWeight := by
  apply NatTrans.ext
  funext i
  rcases i with ⟨i⟩
  cases i with
  | none =>
      change stdSimplex.δ (2 : Fin 3) ≫ stdSimplex.σ (1 : Fin 2) =
        𝟙 (Δ[1] : SSet.{u})
      apply SSet.yonedaEquiv.injective
      decide
  | some i => cases i <;> exact Category.id_comp _

/-- ホーンの一方の辺を潰し、もう一方を区間の生成辺へ送る射。 -/
def loopHornCollapse : loopHornWeight.{u} ⟶ loopIntervalWeight :=
  loopHornToTriangle ≫ loopTriangleToInterval

/-- 区間の 0–1 辺から二単体への包含は、通常の Kan 充填に対して anodyne。 -/
lemma loopIntervalToTriangle_central_anodyne :
    anodyneExtensions (loopIntervalToTriangle.{u}.app (AsSmall.up.obj .one)) := by
  have h₁ : anodyneExtensions (horn₂₁.ι₀₁ : (Δ[1] : SSet.{u}) ⟶ horn 2 1) :=
    MorphismProperty.of_isPushout horn₂₁.isPushout (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.intervalFace_anodyne (1 : Fin 2))
  have h₂ := anodyneExtensions.horn_ι (1 : Fin 3)
  have h := anodyneExtensions.comp_mem horn₂₁.ι₀₁ (horn 2 1).ι h₁ h₂
  rwa [horn.ι_ι] at h

/-- ホーンから共通の二単体への中央の射は、Kan の生成 anodyne 射そのもの。 -/
lemma loopHornToTriangle_central_anodyne :
    anodyneExtensions (loopHornToTriangle.{u}.app (AsSmall.up.obj .one)) :=
  anodyneExtensions.horn_ι (2 : Fin 3)

/-- collapse はホーンの左辺を、向きを保った区間の生成辺へ送る。 -/
lemma loopHornCollapse_leftEdge :
    horn₂₂.ι₀₂ ≫ loopHornCollapse.{u}.app (AsSmall.up.obj .one) =
      𝟙 (Δ[1] : SSet.{u}) := by
  change horn₂₂.ι₀₂ ≫ ((horn 2 2).ι ≫ stdSimplex.σ (1 : Fin 2)) = _
  rw [← Category.assoc, horn.ι_ι]
  apply SSet.yonedaEquiv.injective
  decide

/-- collapse はホーンの右辺を、区間の終点での定値辺へ送る。 -/
lemma loopHornCollapse_rightEdge :
    horn₂₂.ι₁₂ ≫ loopHornCollapse.{u}.app (AsSmall.up.obj .one) =
      SSet.const (X := (Δ[1] : SSet.{u})) (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) := by
  change horn₂₂.ι₁₂ ≫ ((horn 2 2).ι ≫ stdSimplex.σ (1 : Fin 2)) = _
  rw [← Category.assoc, horn.ι_ι]
  apply SSet.yonedaEquiv.injective
  decide

end SerrePositivity.KST.Spectra
