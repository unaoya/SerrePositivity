module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.NerveUnderMap
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialReplacement

/-!
概要：射列をその始点の undercategory に持ち上げる標準図式。
方針：各頂点に始点からの合成射を添え、元の射列の射を三角形に使う。
規約：持ち上げは通常の圏の関手として構成する。
使われ方：Kerodon Construction 5.3.4.7（Tag 026D）、universal scaffold の対角評価。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 概要：射列の始点から全ての頂点への射の自然変換。
方針：有限順序の 0 から各頂点への射を σ で写す。
規約：始域は σ(0) に定値な関手。
使われ方：Kerodon Construction 5.3.4.7（Tag 026D）、undercategory への持ち上げの三角形。 -/
def scaffoldInitialTransformation {C : Type u} [Category.{u} C]
    {n : ℕ} (σ : ComposableArrows C n) :
    (CategoryTheory.Functor.const (Fin (n + 1))).obj (σ.obj 0) ⟶ σ where
  app i := σ.map (homOfLE (Fin.zero_le i))
  naturality i j f := by
    change 𝟙 _ ≫ σ.map (homOfLE _) = σ.map (homOfLE _) ≫ σ.map f
    rw [Category.id_comp, ← σ.map_comp]
    rfl

/-- 概要：射列を始点の undercategory の射列へ持ち上げる。
方針：始点から各頂点への自然変換を Under.lift に渡す。
規約：頂点 0 の矢印は恒等射と等しい。
使われ方：Kerodon Construction 5.3.4.7（Tag 026D）、対角評価に使う標準単体。 -/
def scaffoldUnderChain {C : Type u} [Category.{u} C]
    {n : ℕ} (σ : ComposableArrows C n) : ComposableArrows (Under (σ.obj 0)) n :=
  Under.lift σ (scaffoldInitialTransformation σ)

/-- 概要：標準の undercategory の射列は元の射列へ射影する。
方針：各頂点の射の標的を忘れる定義を計算する。
規約：関手の厳密な等式。
使われ方：Kerodon Construction 5.3.4.7（Tag 026D）、universal scaffold の底の条件。 -/
lemma scaffoldUnderChain_projection {C : Type u} [Category.{u} C]
    {n : ℕ} (σ : ComposableArrows C n) :
    scaffoldUnderChain σ ⋙ Under.forget (σ.obj 0) = σ := rfl

/-- 概要：標準の undercategory の単体を底へ射影すると元の単体になる。
方針：Yoneda の後合成自然性に関手の射影の等式を使う。
規約：単体集合の射として表した標準単体を使う。
使われ方：Kerodon Construction 5.3.4.7（Tag 026D）、対角評価の底上の可換性。 -/
lemma scaffoldUnderChain_yoneda_projection {C : Type u} [Category.{u} C]
    {n : ℕ} (σ : ComposableArrows C n) :
    SSet.yonedaEquiv.symm (scaffoldUnderChain σ) ≫ nerveMap (Under.forget (σ.obj 0)) =
      SSet.yonedaEquiv.symm σ := by
  rw [SSet.yonedaEquiv_symm_comp]
  rfl

/-- 概要：under の標準射列の制限は始点の変化に沿う前合成と可換。
方針：各頂点の構造射の合成則と、忘却関手の忠実性で関手の等式を示す。
規約：α の始点の像への射を Under.map に用いる。
使われ方：Kerodon Construction 5.3.4.7（Tag 026D）、universal scaffold の自然性。 -/
lemma scaffoldUnderChain_restriction {C : Type u} [Category.{u} C]
    {m n : SimplexCategory} (α : m ⟶ n) (σ : ComposableArrows C n.len) :
    (SimplexCategory.toCat.map α).toFunctor ⋙ scaffoldUnderChain σ =
      scaffoldUnderChain ((SimplexCategory.toCat.map α).toFunctor ⋙ σ) ⋙
        Under.map (σ.map (homOfLE (Fin.zero_le (α.toOrderHom 0)))) := by
  refine CategoryTheory.Functor.ext (fun i ↦ ?_) ?_
  · change Under.mk (σ.map (homOfLE _)) =
      Under.mk (σ.map (homOfLE _) ≫ σ.map (homOfLE _))
    rw [← σ.map_comp]
    rfl
  · intro i j f
    apply (Under.forget (σ.obj 0)).map_injective
    simp
    rfl

/-- 概要：under の標準単体の制限と始点の変化は単体集合の射として可換。
方針：射列の関手としての制限公式を Yoneda の自然性で移す。
規約：底の単調写像は任意で、0 を保つことは要求しない。
使われ方：Kerodon Construction 5.3.4.7（Tag 026D）、対角評価の面と退化の整合性。 -/
lemma scaffoldUnderChain_yoneda_restriction {C : Type u} [Category.{u} C]
    {m n : SimplexCategory} (α : m ⟶ n) (σ : ComposableArrows C n.len) :
    stdSimplex.map α ≫ SSet.yonedaEquiv.symm (scaffoldUnderChain σ) =
      SSet.yonedaEquiv.symm
        (scaffoldUnderChain ((SimplexCategory.toCat.map α).toFunctor ⋙ σ)) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.nerveUnderMap (σ.map (homOfLE (Fin.zero_le (α.toOrderHom 0)))) := by
  rw [SSet.yonedaEquiv_symm_naturality_left, SSet.yonedaEquiv_symm_comp]
  exact congrArg (SSet.yonedaEquiv (X := nerve (Under (σ.obj 0))) (n := m)).symm
    (scaffoldUnderChain_restriction α σ)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
