module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseEndpoints
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.Terminal
public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary

/-!
概要：edgewise subdivision の境界充填を join の重みからの射の延長に戻す。
方針：境界の各面を Yoneda の同値で取り出し、面ごとの等式から境界全体を比較する。
規約：この還元自体には Kan 性を要求しない。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、Corollary 5.6.0.6（Tag 028T）、反転比較の射影の充填証明。

対応節は Kerodon 8.1（Tag 03JB）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans

/-- 概要：edgewise の単体を Yoneda 表示した射の単体圏での制限は重みでの前合成。
方針：Yoneda の自然性と subdivision の単体作用素の定義を使う。
規約：α は任意の単体圏の射。
使われ方：Kerodon Construction 8.1.1.1（Tag 03JG）、境界の各面の計算。 -/
lemma edgewiseSubdivision_yoneda_restriction {X : SSet.{u}}
    {m n : SimplexCategory} (α : m ⟶ n) (f : stdSimplex.obj n ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision X) :
    SSet.yonedaEquiv (stdSimplex.map α ≫ f) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.map α ≫ SSet.yonedaEquiv f := by
  rw [← SSet.yonedaEquiv_naturality]
  rfl

/-- 概要：各面で既存の境界と一致する重みの図式は、境界全体を延長する。
方針：境界の射の外延性を面で使い、Yoneda の自然性で面の仮定へ戻す。
規約：n+1 次元の境界を扱う。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、重みの有限部分図式からの充填の回収。 -/
lemma edgewiseSubdivision_boundary_extension {X : SSet.{u}} {n : ℕ}
    (a : (boundary (n + 1) : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision X)
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.obj ⦋n + 1⦌ ⟶ X)
    (hF : ∀ i : Fin (n + 2), _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.map (SimplexCategory.δ i) ≫ F =
      SSet.yonedaEquiv (boundary.ι i ≫ a)) :
    (boundary (n + 1)).ι ≫ SSet.yonedaEquiv.symm F = a := by
  apply boundary.hom_ext
  intro i
  apply SSet.yonedaEquiv.injective
  rw [← Category.assoc, boundary.ι_ι]
  erw [edgewiseSubdivision_yoneda_restriction, SSet.yonedaEquiv.apply_symm_apply]
  exact hF i

/-- 概要：右射影を固定した境界充填は、重みの右半分と各面を固定した延長と同値。
方針：持ち上げの単体を Yoneda で重みの図式へ写し、逆に各面の等式から持ち上げを回収する。
規約：任意の可換な境界正方形を扱い、充填の存在は仮定しない。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、右射影の trivial Kan fibration 性の組み合わせ論への還元。 -/
lemma edgewiseRight_boundary_hasLift_iff {X : SSet.{u}} {n : ℕ}
    (a : (boundary (n + 1) : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision X)
    (b : (Δ[n + 1] : SSet.{u}) ⟶ X)
    (sq : CommSq a (boundary (n + 1)).ι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight X) b) :
    sq.HasLift ↔ ∃ F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.obj ⦋n + 1⦌ ⟶ X,
      (∀ i : Fin (n + 2), _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.map (SimplexCategory.δ i) ≫ F =
        SSet.yonedaEquiv (boundary.ι i ≫ a)) ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[n + 1] : SSet.{u}).op Δ[n + 1] ≫ F = b := by
  constructor
  · intro h
    let _ := h
    refine ⟨SSet.yonedaEquiv sq.lift, ?_, ?_⟩
    · intro i
      rw [← edgewiseSubdivision_yoneda_restriction]
      congr 1
      change stdSimplex.δ i ≫ sq.lift = _
      rw [← boundary.ι_ι i, Category.assoc, sq.fac_left]
    · apply SSet.yonedaEquiv.injective
      have h := congrArg SSet.yonedaEquiv sq.fac_right
      exact h
  · rintro ⟨F, hF, hR⟩
    refine CommSq.HasLift.mk'
      { l := SSet.yonedaEquiv.symm F
        fac_left := edgewiseSubdivision_boundary_extension a F hF
        fac_right := ?_ }
    apply SSet.yonedaEquiv.injective
    erw [SSet.yonedaEquiv_comp, SSet.yonedaEquiv.apply_symm_apply]
    exact congrArg SSet.yonedaEquiv hR

/-- 概要：右端射影の零次元の境界は常に充填できる。
方針：指定された頂点の恒等辺を定値な重みの図式として取り、零次元の境界の空性を使う。
規約：X の Kan 性は不要。
使われ方：Kerodon Notation 8.1.1.6（Tag 03JK）、右射影の境界充填の初期段階。 -/
lemma edgewiseRight_boundary_zero_lifting (X : SSet.{u}) :
    HasLiftingProperty (boundary.{u} 0).ι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight X) := by
  constructor
  intro a b sq
  let F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.obj ⦋0⦌ ⟶ X := SSet.const (SSet.yonedaEquiv b)
  refine CommSq.HasLift.mk'
    { l := SSet.yonedaEquiv.symm F
      fac_left := boundary.hom_ext₀
      fac_right := ?_ }
  apply SSet.yonedaEquiv.injective
  erw [SSet.yonedaEquiv_comp, SSet.yonedaEquiv.apply_symm_apply]
  change X.map (SimplexCategory.const ⦋0⦌ ⦋0⦌ 0).op (SSet.yonedaEquiv b) = SSet.yonedaEquiv b
  have hc : SimplexCategory.const ⦋0⦌ ⦋0⦌ 0 = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
  rw [hc]
  exact CategoryTheory.Functor.map_id_apply X _ _

/-- 概要：右射影の trivial Kan fibration 性は、正次元の重みの各面と右半分を保つ延長から従う。
方針：全境界による判定を使い、零次元を恒等辺で、正次元を重みの延長との同値で処理する。
規約：延長仮定の証明はこの補題には含めない。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、Kan 充填から反転比較の同値性へ進むための還元。 -/
lemma edgewiseRight_trivialKanFibration_of_extensions (X : SSet.{u})
    (h : ∀ (n : ℕ) (a : (boundary (n + 1) : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision X)
      (b : (Δ[n + 1] : SSet.{u}) ⟶ X)
      (_ : CommSq a (boundary (n + 1)).ι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight X) b),
      ∃ F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.obj ⦋n + 1⦌ ⟶ X,
        (∀ i : Fin (n + 2), _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.map (SimplexCategory.δ i) ≫ F =
          SSet.yonedaEquiv (boundary.ι i ≫ a)) ∧
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[n + 1] : SSet.{u}).op Δ[n + 1] ≫ F = b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight X) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibration_iff_boundary]
  intro n
  cases n with
  | zero => exact edgewiseRight_boundary_zero_lifting X
  | succ n =>
    constructor
    intro a b sq
    exact (edgewiseRight_boundary_hasLift_iff a b sq).2 (h n a b sq)

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
