module
public import SerrePositivity.InfinityCategories.Core.Cocone
public import SerrePositivity.InfinityCategories.Core.InitialUniqueness
public import SerrePositivity.InfinityCategories.Core.JoinLifting

/-! # join の面から coslice の境界充填へ

概要：join 上の写像が coslice 境界の全ての面と一致すれば、coslice の境界充填を与える。
方針：左因子の固定条件を一面から取り出し、curry と uncurry で全ての面を比較する。
規約：値域の quasicategory 性は不要。使われ方：D7 の標準 cofiber 余錐の始対象性。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory
open scoped Simplicial

/-- 概要：最初の頂点に指定した余錐は uncurry した境界のその頂点への制限で回収できる。
方針：指定頂点の式を uncurry し、前合成と Yoneda の公式を使う。
規約：最初の頂点は零番。使われ方：cofiber 余錐の二脚とホモトピーの回収。 -/
lemma cosliceBoundary_first_cocone {K X : SSet.{u}} {p : K ⟶ X} {n : ℕ}
    (b : (SSet.boundary (n + 1) : SSet.{u}) ⟶ sliceUnder p) (c : JoinCocone p)
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm c) :
    joinMap (𝟙 K) (boundaryVertex n 0) ≫ sliceUnderUncurry b = c.val := by
  have h := congrArg sliceUnderUncurry hb
  rw [sliceUnderUncurry_precomp] at h
  exact h.trans (sliceUnderUncurry_yoneda 0 c)

/-- 概要：join の全境界面が coslice 境界に一致する写像は左因子上で指定図式に等しい。
方針：零番目の面を左包含で評価し、uncurry の固定条件を使う。
規約：全ての正次元の境界。使われ方：join の充填を coslice へ curry する。 -/
lemma cosliceJoinBoundaryFaces_fixed {n : ℕ} {K X : SSet.{u}} (p : K ⟶ X)
    (b : (SSet.boundary (n + 1) : SSet.{u}) ⟶ sliceUnder p)
    (F : join K (Δ[n + 1] : SSet.{u}) ⟶ X)
    (hfaces : ∀ j : Fin (n + 2), joinMap (𝟙 K) (SSet.stdSimplex.δ j) ≫ F =
      joinMap (𝟙 K) (SSet.boundary.ι j) ≫ sliceUnderUncurry b) :
    joinInl K Δ[n + 1] ≫ F = p := by
  have h := congrArg (fun T ↦ joinInl K (Δ[n] : SSet.{u}) ≫ T) (hfaces 0)
  simpa only [← Category.assoc, joinInl_joinMap, Category.id_comp,
    sliceUnderUncurry_fixed] using h

/-- 概要：join の全ての面が元の coslice 境界と一致すれば curry は境界を延長する。
方針：境界の面の外延性と uncurry の単射性を使う。
規約：図式の固定条件は全境界面の一致から導く。使われ方：cofiber の直接充填の最終段階。 -/
lemma sliceUnderCurry_boundary_of_joinFaces {n : ℕ} {K X : SSet.{u}} (p : K ⟶ X)
    (b : (SSet.boundary (n + 1) : SSet.{u}) ⟶ sliceUnder p)
    (F : join K (Δ[n + 1] : SSet.{u}) ⟶ X)
    (hfaces : ∀ j : Fin (n + 2), joinMap (𝟙 K) (SSet.stdSimplex.δ j) ≫ F =
      joinMap (𝟙 K) (SSet.boundary.ι j) ≫ sliceUnderUncurry b) :
    (SSet.boundary (n + 1)).ι ≫
      sliceUnderCurry F (cosliceJoinBoundaryFaces_fixed p b F hfaces) = b := by
  apply SSet.boundary.hom_ext
  intro j
  rw [← Category.assoc, SSet.boundary.ι_ι]
  apply sliceUnderUncurry_injective p
  rw [sliceUnderUncurry_precomp, sliceUnderUncurry_curry, sliceUnderUncurry_precomp]
  exact hfaces j

end SerrePositivity.InfinityCategories
