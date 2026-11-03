module
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import SerrePositivity.InfinityCategories.Core.Coslice
public import SerrePositivity.InfinityCategories.Core.Join
public import SerrePositivity.InfinityCategories.Core.JoinLifting
public import SerrePositivity.InfinityCategories.Core.Slice
public import SerrePositivity.InfinityCategories.Core.VertexFiber
public import SerrePositivity.InfinityCategories.F1.Joins.CosliceTriangleFiber
public import SerrePositivity.InfinityCategories.F1.CoconeMappingGluing
public import SerrePositivity.InfinityCategories.F1.CoconeMappingSpace

/-! # 二枝の余錐空間の引き戻し表示

概要：span から指定終点への余錐の空間は、両枝の余錐空間の共通始点上の引き戻しとなる。
方針：ホーンの二枝の pushout と、終点固定の余錐の貼り合わせの普遍性を使う。
規約：値域の quasicategory 性は不要。使われ方：HA Lemma 1.1.2.10 の D(σ) の模型。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：右枝の余錐を共通始点へ制限し、左枝側の始点の表示へ移す。
方針：ホーンの二包含の共通始点の等号で終域を輸送する。
規約：終点は同じ y。使われ方：余錐空間の引き戻しの右脚。 -/
def spanCoconeMappingRightBase {X : SSet.{u}}
    (p : (horn 2 0 : SSet.{u}) ⟶ X) (y : X _⦋0⦌) :
    coconeMappingSpace (horn₂₀.ι₀₂ ≫ p) y ⟶
      coconeMappingSpace (stdSimplex.δ (1 : Fin 2) ≫ horn₂₀.ι₀₁ ≫ p) y :=
  cosliceRestrictionFiberMap (horn₂₀.ι₀₂ ≫ p) (stdSimplex.δ (1 : Fin 2)) y ≫
    eqToHom (congrArg (fun q => coconeMappingSpace q y)
      (congrArg (fun i => i ≫ p) horn₂₀.isPushout.w.symm))

/-- 概要：共通始点の表示の変更を含む右脚も、uncurry 後には通常の制限となる。
方針：等号の輸送が余錐を変えないことと制限の式を組み合わせる。
規約：任意パラメーター。使われ方：引き戻しの可換性と普遍性。 -/
lemma spanCoconeMappingRightBase_uncurry {X T : SSet.{u}}
    (p : (horn 2 0 : SSet.{u}) ⟶ X) (y : X _⦋0⦌)
    (a : T ⟶ coconeMappingSpace (horn₂₀.ι₀₂ ≫ p) y) :
    sliceUnderUncurry ((a ≫ spanCoconeMappingRightBase p y) ≫
      vertexFiberι (sliceUnderProjection (stdSimplex.δ (1 : Fin 2) ≫ horn₂₀.ι₀₁ ≫ p)) y) =
    joinMap (stdSimplex.δ (1 : Fin 2)) (𝟙 T) ≫
      sliceUnderUncurry (a ≫ vertexFiberι (sliceUnderProjection (horn₂₀.ι₀₂ ≫ p)) y) := by
  exact coconeMappingSpace_restrict_change_uncurry (horn₂₀.ι₀₂ ≫ p)
    (stdSimplex.δ (1 : Fin 2)) (congrArg (fun i => i ≫ p) horn₂₀.isPushout.w.symm) y a

/-- 概要：二枝から共通始点へ制限した終点固定の余錐は一致する。
方針：uncurry 後に二つの共通始点の包含を比較する。
規約：図式の表示の輸送を含む厳密な等号。使われ方：引き戻しの可換性。 -/
lemma spanCoconeMapping_restriction_comm {X : SSet.{u}}
    (p : (horn 2 0 : SSet.{u}) ⟶ X) (y : X _⦋0⦌) :
    cosliceRestrictionFiberMap p horn₂₀.ι₀₁ y ≫
      cosliceRestrictionFiberMap (horn₂₀.ι₀₁ ≫ p) (stdSimplex.δ (1 : Fin 2)) y =
    cosliceRestrictionFiberMap p horn₂₀.ι₀₂ y ≫ spanCoconeMappingRightBase p y := by
  apply vertexFiber_hom_ext
  apply sliceUnderUncurry_injective
  rw [coconeMappingSpace_restrict_uncurry, spanCoconeMappingRightBase_uncurry]
  have hL := coconeMappingSpace_restrict_uncurry p horn₂₀.ι₀₁ y (𝟙 _)
  have hR := coconeMappingSpace_restrict_uncurry p horn₂₀.ι₀₂ y (𝟙 _)
  simp only [Category.id_comp] at hL hR
  rw [hL, hR]
  simp only [← Category.assoc, ← joinMap_comp, horn₂₀.isPushout.w]

/-- 概要：span の余錐空間は、両枝の余錐空間の共通始点上の厳密な引き戻し。
方針：任意パラメーターの二枝の余錐の存在と一意性を適用する。
規約：値域の Kan 性や quasicategory 性は不要。使われ方：二枝交換とループ反転の比較。 -/
lemma spanCoconeMapping_isPullback {X : SSet.{u}}
    (p : (horn 2 0 : SSet.{u}) ⟶ X) (y : X _⦋0⦌) :
    IsPullback (cosliceRestrictionFiberMap p horn₂₀.ι₀₁ y)
      (cosliceRestrictionFiberMap p horn₂₀.ι₀₂ y)
      (cosliceRestrictionFiberMap (horn₂₀.ι₀₁ ≫ p) (stdSimplex.δ (1 : Fin 2)) y)
      (spanCoconeMappingRightBase p y) := by
  apply IsPullback.mk' (spanCoconeMapping_restriction_comm p y)
  · intro T a b ha hb
    exact coconeMappingSpace_hom_ext_of_pushout horn₂₀.isPushout p y ha hb
  · intro T b c hbc
    have h := congrArg (fun f => sliceUnderUncurry (f ≫
      vertexFiberι (sliceUnderProjection (stdSimplex.δ (1 : Fin 2) ≫ horn₂₀.ι₀₁ ≫ p)) y)) hbc
    rw [coconeMappingSpace_restrict_uncurry, spanCoconeMappingRightBase_uncurry] at h
    exact exists_coconeMappingSpace_glue horn₂₀.isPushout p y b c h

end SerrePositivity.InfinityCategories
