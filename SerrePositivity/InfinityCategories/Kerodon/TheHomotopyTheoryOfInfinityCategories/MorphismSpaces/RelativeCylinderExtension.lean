module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PushoutHomotopy

/-!
概要：図式を固定する可逆ホモトピーの円柱への延長。
方針：共通部分で二つの端を貼り、定値族からの自然同型を単射に沿って延長する。
規約：両端を含む射が単射であることを要求する。
使われ方：Kerodon Lemma 4.6.4.25（Tag 01KV） の相対的な円柱の構成。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：共通部分を固定した可逆ホモトピーの両端は、単射な円柱の両端へ延長できる。
方針：第一端の恒等ホモトピーと第二端の指定ホモトピーを pushout で貼り、自然同型を延長する。
規約：円柱は両端の共通の射影を持ち、共通部分で端点が一致する。
使われ方：Kerodon Lemma 4.6.4.25（Tag 01KV） の join の円柱への延長。 -/
lemma exists_relativeCylinder_extension {K T C Q X : SSet.{u}} [Quasicategory X]
    (a : K ⟶ T) (r s : T ⟶ C) (hP : IsPushout a a r s)
    (t : C ⟶ Q) [Mono t] (q : Q ⟶ T)
    (hr : r ≫ t ≫ q = 𝟙 T) (hs : s ≫ t ≫ q = 𝟙 T)
    (f g : T ⟶ X) (hfg : a ≫ f = a ≫ g) (H : SSet.Homotopy f g)
    (hH : (a ▷ (Δ[1] : SSet.{u})) ≫ H.h = fst K Δ[1] ≫ a ≫ f)
    (hI : ∀ x, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H x).toTruncated) :
    ∃ F : Q ⟶ X, r ≫ t ≫ F = f ∧ s ≫ t ≫ F = g := by
  let v := hP.desc f g hfg
  let u := q ≫ f
  have hru : r ≫ t ≫ u = f := by simp only [u, ← Category.assoc, hr, Category.id_comp]
  have hsu : s ≫ t ≫ u = f := by simp only [u, ← Category.assoc, hs, Category.id_comp]
  have hrv : r ≫ v = f := hP.inl_desc _ _ _
  have hsv : s ≫ v = g := hP.inr_desc _ _ _
  let L : SSet.Homotopy (r ≫ t ≫ u) (r ≫ v) := {
    h := fst T (Δ[1] : SSet.{u}) ≫ f
    h₀ := by rw [← Category.assoc, SSet.ι₀_fst, Category.id_comp]; exact hru.symm
    h₁ := by rw [← Category.assoc, SSet.ι₁_fst, Category.id_comp]; exact hrv.symm
    rel := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro z
      exact False.elim z.1.property }
  let R : SSet.Homotopy (s ≫ t ≫ u) (s ≫ v) := {
    h := H.h
    h₀ := H.h₀.trans hsu.symm
    h₁ := H.h₁.trans hsv.symm
    rel := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro z
      exact False.elim z.1.property }
  have hw : (a ▷ (Δ[1] : SSet.{u})) ≫ L.h = (a ▷ (Δ[1] : SSet.{u})) ≫ R.h := by
    change (a ▷ (Δ[1] : SSet.{u})) ≫ fst T Δ[1] ≫ f = _
    rw [← Category.assoc, whiskerRight_fst, Category.assoc]
    exact hH.symm
  have hL : ∀ x, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge L x).toTruncated := by
    intro x
    have hId : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (SSet.Truncated.Edge.id (X := (truncation 2).obj T) x) := by
      change IsIso (SSet.Truncated.HomotopyCategory.homMk _)
      rw [SSet.Truncated.HomotopyCategory.homMk_id]
      infer_instance
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr
      (e := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge L x).toTruncated)
      (f := (SSet.Truncated.Edge.id (X := (truncation 2).obj T) x).map
        ((truncation 2).map f)) rfl).2 (hId.map f)
  obtain ⟨e⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.nonempty_functorIso_of_pushout_homotopies hP L R hw hL
    (fun x ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr
      (e := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge R x).toTruncated)
      (f := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H x).toTruncated) rfl).2 (hI x))
  obtain ⟨F, hF⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.exists_extension_of_functorIso t u v e
  refine ⟨F, ?_, ?_⟩
  · rw [hF]
    exact hrv
  · rw [hF]
    exact hsv

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
