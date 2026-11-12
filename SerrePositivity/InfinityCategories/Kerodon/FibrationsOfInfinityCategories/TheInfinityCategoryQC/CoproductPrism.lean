module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.PrismContraction

/-!
概要：二項 coproduct 上の指定 prism の貼り合わせ。
方針：左直積の coproduct 保存を使う。
規約：形状の quasicategory 性は不要。
使われ方：極限錐の頂点を固定した図式の輸送。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

/-- 概要：二つの指定 prism を coproduct 上の一つの prism に貼る。
方針：区間との直積の二項 coproduct 保存同型を使う。
規約：時刻の標準区間は第一因子。
使われ方：錐の頂点と図式の比較を一緒に指定する。 -/
def coprodPrism {A B X : SSet.{u}}
    (H : (Δ[1] : SSet.{u}) ⊗ A ⟶ X) (J : (Δ[1] : SSet.{u}) ⊗ B ⟶ X) :
    (Δ[1] : SSet.{u}) ⊗ (A ⨿ B) ⟶ X :=
  (PreservesColimitPair.iso (tensorLeft (Δ[1] : SSet.{u})) A B).inv ≫ coprod.desc H J
/-- 概要：貼った prism の左因子への制限は元の左の prism。
方針：coproduct 比較同型と左包含の式を計算する。
規約：全時刻の厳密な等式。
使われ方：頂点を固定するホモトピーの照合。 -/
lemma coprodPrism_inl {A B X : SSet.{u}}
    (H : (Δ[1] : SSet.{u}) ⊗ A ⟶ X) (J : (Δ[1] : SSet.{u}) ⊗ B ⟶ X) :
    (Δ[1] ◁ (coprod.inl : A ⟶ A ⨿ B)) ≫ coprodPrism H J = H := by
  let e := PreservesColimitPair.iso (tensorLeft (Δ[1] : SSet.{u})) A B
  have h : (coprod.inl : (Δ[1] ⊗ A) ⟶ (Δ[1] ⊗ A) ⨿ (Δ[1] ⊗ B)) ≫ e.hom =
      (Δ[1] ◁ (coprod.inl : A ⟶ A ⨿ B)) := by
    change coprod.inl ≫ coprodComparison (tensorLeft Δ[1]) A B = _
    simp [coprodComparison]
  change _ ≫ (e.inv ≫ _) = _
  rw [← h, Category.assoc, Iso.hom_inv_id_assoc, coprod.inl_desc]
/-- 概要：貼った prism の右因子への制限は元の右の prism。
方針：coproduct 比較同型と右包含の式を計算する。
規約：全時刻の厳密な等式。
使われ方：元の図式の指定自然変換の照合。 -/
lemma coprodPrism_inr {A B X : SSet.{u}}
    (H : (Δ[1] : SSet.{u}) ⊗ A ⟶ X) (J : (Δ[1] : SSet.{u}) ⊗ B ⟶ X) :
    (Δ[1] ◁ (coprod.inr : B ⟶ A ⨿ B)) ≫ coprodPrism H J = J := by
  let e := PreservesColimitPair.iso (tensorLeft (Δ[1] : SSet.{u})) A B
  have h : (coprod.inr : (Δ[1] ⊗ B) ⟶ (Δ[1] ⊗ A) ⨿ (Δ[1] ⊗ B)) ≫ e.hom =
      (Δ[1] ◁ (coprod.inr : B ⟶ A ⨿ B)) := by
    change coprod.inr ≫ coprodComparison (tensorLeft Δ[1]) A B = _
    simp [coprodComparison]
  change _ ≫ (e.inv ≫ _) = _
  rw [← h, Category.assoc, Iso.hom_inv_id_assoc, coprod.inr_desc]
/-- 概要：貼った prism の端点は元の端点二つからの標準射。
方針：左右の包含に制限し、端点包含の自然性を使う。
規約：両端点を共通の式で扱う。
使われ方：指定した元と置換後の図式の条件。 -/
lemma coprodPrism_endpoint {A B X : SSet.{u}} (k : Fin 2)
    (H : (Δ[1] : SSet.{u}) ⊗ A ⟶ X) (J : (Δ[1] : SSet.{u}) ⊗ B ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint k (A ⨿ B) ≫ coprodPrism H J =
      coprod.desc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint k A ≫ H) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint k B ≫ J) := by
  apply coprod.hom_ext
  · rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, Category.assoc,
      coprodPrism_inl, coprod.inl_desc]
  · rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, Category.assoc,
      coprodPrism_inr, coprod.inr_desc]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
