module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseCoverDomain
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseOneBoundary
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.KanFibrationTools
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：Kan 複体の edgewise の右端射影の全境界充填。
方針：全正次元の境界を被覆上で接合し、延長領域の同定と Kan 延長を使う。
規約：零次元は既存の恒等辺による充填を用い、モデル構造の弱同値は使わない。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、Corollary 5.6.0.6（Tag 028T）、自然な反転比較の右側の同値。

対応節は Kerodon 8.1（Tag 03JB）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans

/-- 概要：右射影の正次元の境界データを各面と右半分を固定したまま重み全体へ延長できる。
方針：像の被覆上の接合と正則 pairing による Kan 延長を合成する。
規約：全体の次数は n+1 で一次元も含む。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、右射影の境界充填の存在。 -/
lemma exists_edgewiseRight_weight_extension {K : SSet.{u}} [KanComplex K] {n : ℕ}
    (a : (boundary (n + 1) : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision K)
    (b : (Δ[n + 1] : SSet.{u}) ⟶ K)
    (sq : CommSq a (boundary (n + 1)).ι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight K) b) :
    ∃ F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.obj ⦋n + 1⦌ ⟶ K,
      (∀ i : Fin (n + 2), _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.map (SimplexCategory.δ i) ≫ F =
        SSet.yonedaEquiv (boundary.ι i ≫ a)) ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[n + 1] : SSet.{u}).op Δ[n + 1] ≫ F = b := by
  let X : Option (Fin (n + 2)) → SSet.{u} := fun
    | none => Δ[n + 1]
    | some _ => _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.obj ⦋n⦌
  let ι : ∀ i, X i ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.obj ⦋n + 1⦌ := fun
    | none => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[n + 1] : SSet.{u}).op Δ[n + 1]
    | some i => _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.map (SimplexCategory.δ i)
  let f : ∀ i, X i ⟶ K := fun
    | none => b
    | some i => SSet.yonedaEquiv (boundary.ι i ≫ a)
  have hcomp : ∀ (i j : Option (Fin (n + 2))) (d : SimplexCategoryᵒᵖ)
      (x : (X i).obj d) (y : (X j).obj d),
      (ι i).app d x = (ι j).app d y → (f i).app d x = (f j).app d y := by
    intro i j d x y hxy
    cases i with
    | none =>
      cases j with
      | none =>
        have he : x = y := (mono_iff_injective
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[n + 1] : SSet.{u}).op Δ[n + 1]).app d)).mp inferInstance hxy
        subst y
        rfl
      | some j => exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseBoundaryFace_right_compatible a b sq j d y x hxy.symm).symm
    | some i =>
      cases j with
      | none => exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseBoundaryFace_right_compatible a b sq i d x y hxy
      | some j => exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseBoundaryFaces_compatible_all a i j d x y hxy
  obtain ⟨G, hG⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.exists_map_of_compatible_range_cover X ι f hcomp
  let C : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.obj ⦋n + 1⦌).Subcomplex := ⨆ i, Subcomplex.range (ι i)
  have hD : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRightWeightDomain (n + 1) = C := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRightWeightDomain_eq_face_cover]
    apply le_antisymm
    · refine sup_le ?_ (iSup_le (fun i ↦ ?_))
      · exact le_iSup (fun j ↦ Subcomplex.range (ι j)) none
      · exact le_iSup (fun j ↦ Subcomplex.range (ι j)) (some i)
    · apply iSup_le
      intro i
      cases i with
      | none => exact le_sup_left
      | some i =>
        exact le_trans (le_iSup (fun k : Fin (n + 2) ↦
          Subcomplex.range (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.{u}.map (SimplexCategory.δ k))) i) le_sup_right
  obtain ⟨F, hF⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.exists_edgewiseRightWeightDomain_extension (n + 1)
    (Subcomplex.homOfLE hD.le ≫ G)
  have hCF : C.ι ≫ F = G := by
    have h := congrArg (fun g ↦ Subcomplex.homOfLE hD.ge ≫ g) hF
    change C.ι ≫ F = Subcomplex.homOfLE hD.ge ≫ Subcomplex.homOfLE hD.le ≫ G at h
    have he : Subcomplex.homOfLE hD.ge ≫ Subcomplex.homOfLE hD.le = 𝟙 (C : SSet.{u}) := rfl
    rw [← Category.assoc, he, Category.id_comp] at h
    exact h
  have hcover : ∀ i, ι i ≫ F = f i := by
    intro i
    calc
      _ = (Subcomplex.lift (ι i) (le_iSup (fun j ↦ Subcomplex.range (ι j)) i) ≫ C.ι) ≫ F := by
        rw [Subcomplex.lift_ι]
      _ = f i := by rw [Category.assoc, hCF, hG i]
  exact ⟨F, fun i ↦ hcover (some i), hcover none⟩

/-- 概要：Kan 複体の edgewise の右端射影は trivial Kan fibration。
方針：正次元の重みの延長と零次元の恒等辺から全境界の充填を得る。
規約：全境界を持ち上げることが結論であり、対象ごとの同値だけではない。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、空間値図式の自然な反転比較の右射影。 -/
@[kerodon 048J, kerodon 04FA]
instance edgewiseRight_trivialKanFibration (K : SSet.{u}) [KanComplex K] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight K) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight_trivialKanFibration_of_extensions K
    (fun _ a b sq ↦ exists_edgewiseRight_weight_extension a b sq)

/-- 概要：Kan 複体の edgewise subdivision は Kan 複体。
方針：右端射影の全単射に対する持ち上げ性からホーンの持ち上げ性を制限し、終対象への射で合成する。
規約：既存の Fibration クラスはホーンの rlp としてだけ使う。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、両端の同値を結ぶ Kan な共通始域。 -/
@[kerodon 048H]
instance edgewiseSubdivision_kanComplex (K : SSet.{u}) [KanComplex K] :
    KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision K) := by
  haveI : HomotopicalAlgebra.Fibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight K) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.fibration_of_hasLiftingProperty_horn (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight K)
      (fun _ _ ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem _ inferInstance)
  exact HomotopicalAlgebra.isFibrant_of_fibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight K)

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
