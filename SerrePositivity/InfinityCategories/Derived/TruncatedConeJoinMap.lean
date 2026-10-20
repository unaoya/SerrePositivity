module
public import SerrePositivity.InfinityCategories.Derived.TruncatedConeCoslice
public import SerrePositivity.InfinityCategories.Derived.BoundedSimplicialExtension
public import SerrePositivity.InfinityCategories.Core.RightFibration
public import SerrePositivity.InfinityCategories.Core.Limit

/-! # 有界な図式の切断錐から実 join 錐へ

概要：次元上界までの整合錐データから、元の図式を厳密に延長する実 join 写像を作る。
方針：共通 apex の coslice への切断写像を一意に延長し、uncurry する。
規約：apex は同じ指定頂点を保つ。使われ方：実 Verdier over の有限錐。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet Opposite
open scoped Simplicial
variable {K X : SSet.{u}} {f : K ⟶ X} {N : ℕ} [K.HasDimensionLE N]
variable (C : TruncatedJoinConeData f N)

/-- 切断錐が定める、共通 apex の実 coslice への全単体写像。 -/
def TruncatedJoinConeData.cosliceExtension : K ⟶ sliceUnderVertex C.apex :=
  boundedSimplicialExtension C.cosliceMap

/-- coslice への延長は全図式の上で射影と厳密に可換。 -/
lemma TruncatedJoinConeData.cosliceExtension_projection :
    C.cosliceExtension ≫ sliceUnderProjection (SSet.yonedaEquiv.symm C.apex) = f := by
  apply boundedSimplicialHom_ext (N := N)
  have he : (truncation N).map C.cosliceExtension = C.cosliceMap :=
    boundedSimplicialExtension_truncation C.cosliceMap
  exact ((truncation N).map_comp C.cosliceExtension
    (sliceUnderProjection (SSet.yonedaEquiv.symm C.apex))).trans
      ((congrArg (fun g => g ≫
        (truncation N).map (sliceUnderProjection (SSet.yonedaEquiv.symm C.apex))) he).trans
          C.cosliceMap_projection)

/-- 同じ apex を前置し、図式全体を延長する実 join 写像。 -/
def TruncatedJoinConeData.joinMap : join (Δ[0] : SSet.{u}) K ⟶ X :=
  sliceUnderUncurry C.cosliceExtension

/-- 実 join 写像の左制限は指定された同じ apex。 -/
lemma TruncatedJoinConeData.joinMap_left :
    joinInl (Δ[0] : SSet.{u}) K ≫ C.joinMap = SSet.yonedaEquiv.symm C.apex :=
  sliceUnderUncurry_fixed C.cosliceExtension

/-- 実 join 写像の右制限は元の図式と厳密に一致する。 -/
lemma TruncatedJoinConeData.joinMap_right :
    joinInr (Δ[0] : SSet.{u}) K ≫ C.joinMap = f := by
  exact (sliceUnderUncurry_projection C.cosliceExtension).trans C.cosliceExtension_projection

/-- 次元上界までの切断錐から得る、元の図式の実 join 錐。 -/
def TruncatedJoinConeData.joinCone : JoinCone f :=
  ⟨C.joinMap, C.joinMap_right⟩

/-- 得られる実錐の頂点は指定された同じ apex。 -/
lemma TruncatedJoinConeData.joinCone_vertex : C.joinCone.vertex = C.apex := by
  rw [JoinCone.vertex_eq]
  change SSet.yonedaEquiv (joinInl (Δ[0] : SSet.{u}) K ≫ C.joinMap) = _
  rw [C.joinMap_left, Equiv.apply_symm_apply]

/-- 指定低次数単体への実 join 写像の制限は、入力の同じ錐単体である。 -/
lemma TruncatedJoinConeData.joinMap_simplex (n : ℕ) (hn : n ≤ N) (σ : K _⦋n⦌) :
    SerrePositivity.InfinityCategories.joinMap (𝟙 (Δ[0] : SSet.{u}))
        (SSet.yonedaEquiv.symm σ) ≫ C.joinMap =
      (pointJoinStdSimplexIso n).hom ≫ SSet.yonedaEquiv.symm (C.simplex n hn σ) := by
  have happ : C.cosliceExtension.app (op ⦋n⦌) σ = C.cosliceSimplex n hn σ :=
    boundedSimplicialExtensionApp_low C.cosliceMap hn σ
  calc
    _ = sliceUnderUncurry (SSet.yonedaEquiv.symm σ ≫ C.cosliceExtension) :=
      (sliceUnderUncurry_precomp C.cosliceExtension (SSet.yonedaEquiv.symm σ)).symm
    _ = sliceUnderUncurry (SSet.yonedaEquiv.symm (C.cosliceSimplex n hn σ)) := by
      rw [SSet.yonedaEquiv_symm_comp]
      exact congrArg (fun z : (sliceUnderVertex C.apex) _⦋n⦌ =>
        sliceUnderUncurry (SSet.yonedaEquiv.symm z)) happ
    _ = _ := sliceUnderUncurry_yoneda n (C.cosliceSimplex n hn σ)

end SerrePositivity.InfinityCategories
