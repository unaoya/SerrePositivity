module
public import SerrePositivity.KST.SConstruction.PointedExtensionSpace
public import SerrePositivity.KST.Spectra.PointedMappingHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TerminalUniqueness

/-! # 点つき延長の選択のホモトピー比較
概要：指定した射の二つの anodyne 延長は実際の基点固定ホモトピーで比較できる。
方針：延長を可縮な選択空間の頂点へ戻し、その間の辺を写像空間へ写す。
規約：源の Kan 性は不要。使われ方：Kan な随伴射の選択独立性と自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：実際の点つき延長を選択空間の頂点にする。
方針：前合成の頂点の式を pullback の固定条件へ渡す。
規約：延長の等式を明示する。使われ方：任意の延長同士の比較。 -/
def pointedExtensionVertex {A B Z : PointedSimplicialSet.{u}} (i : A ⟶ B) (h : A ⟶ Z)
    (k : B ⟶ Z) (hk : i ≫ k = h) : (pointedExtensionSpace i h) _⦋0⦌ :=
  SSet.yonedaEquiv (pullback.lift
    (f := (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i Z).right)
    (g := SSet.yonedaEquiv.symm (Spectra.PointedMapping.familyVertex h))
    (SSet.yonedaEquiv.symm (Spectra.PointedMapping.familyVertex k)) (𝟙 (Δ[0] : SSet.{u})) (by
      apply SSet.yonedaEquiv.injective
      rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply,
        Spectra.PointedMapping.familyVertex_pre, hk, Category.id_comp, Equiv.apply_symm_apply]))

/-- 概要：延長から作った選択頂点の第一射影は元の射の頂点。
方針：Yoneda の自然性と pullback の第一射影の式。
規約：厳密等号。使われ方：辺の端点の照合。 -/
lemma pointedExtensionVertex_projection {A B Z : PointedSimplicialSet.{u}} (i : A ⟶ B) (h : A ⟶ Z)
    (k : B ⟶ Z) (hk : i ≫ k = h) :
    (pullback.fst (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i Z).right
      (SSet.yonedaEquiv.symm (Spectra.PointedMapping.familyVertex h))).app (Opposite.op ⦋0⦌)
        (pointedExtensionVertex i h k hk) = Spectra.PointedMapping.familyVertex k := by
  unfold pointedExtensionVertex
  erw [← SSet.yonedaEquiv_comp, pullback.lift_fst, Equiv.apply_symm_apply]

/-- 概要：二つの点つき anodyne 延長の間に写像空間の辺が存在する。
方針：可縮な選択空間の二頂点を終対象性で結び、第一射影で写す。
規約：標的は Kan。使われ方：実際の基点固定ホモトピーの構成。 -/
lemma pointedExtensions_nonempty_mappingEdge {A B Z : PointedSimplicialSet.{u}}
    (i : A ⟶ B) (hi : anodyneExtensions i.right) (h : A ⟶ Z) [KanComplex Z.right]
    (k l : B ⟶ Z) (hk : i ≫ k = h) (hl : i ≫ l = h) :
    Nonempty ((PointedObject.basedHom B Z).right.Edge
      (Spectra.PointedMapping.familyVertex k) (Spectra.PointedMapping.familyVertex l)) := by
  let v := pointedExtensionVertex i h k hk
  let w := pointedExtensionVertex i h l hl
  have hc := pointedExtensionSpace_isContractibleKan i hi h
  obtain ⟨e⟩ := (hc.isTerminalVertex w).nonempty_edge v
  let p := pullback.fst (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i Z).right
    (SSet.yonedaEquiv.symm (Spectra.PointedMapping.familyVertex h))
  have he := SSet.Edge.map (SSet.Edge.ofTruncated e) p
  have hv := pointedExtensionVertex_projection i h k hk
  have hw := pointedExtensionVertex_projection i h l hl
  change p.app (Opposite.op ⦋0⦌) v = Spectra.PointedMapping.familyVertex k at hv
  change p.app (Opposite.op ⦋0⦌) w = Spectra.PointedMapping.familyVertex l at hw
  erw [hv, hw] at he
  exact ⟨he⟩

/-- 概要：二つの点つき anodyne 延長は基点固定ホモトピーで比較できる。
方針：写像空間の辺を L9 の実際のホモトピーへ戻す。
規約：源の Kan 性は不要。使われ方：延長の選択独立性。 -/
lemma pointedExtensions_homotopy {A B Z : PointedSimplicialSet.{u}}
    (i : A ⟶ B) (hi : anodyneExtensions i.right) (h : A ⟶ Z) [KanComplex Z.right]
    (k l : B ⟶ Z) (hk : i ≫ k = h) (hl : i ≫ l = h) :
    ∃ H : SSet.Homotopy k.right l.right,
      B.hom ▷ (Δ[1] : SSet.{u}) ≫ H.h = toUnit (𝟙_ SSet.{u} ⊗ (Δ[1] : SSet.{u})) ≫ Z.hom := by
  obtain ⟨e⟩ := pointedExtensions_nonempty_mappingEdge i hi h k l hk hl
  exact ⟨Spectra.PointedMapping.homotopyOfEdge e, Spectra.PointedMapping.homotopyOfEdge_base e⟩

end SerrePositivity.KST.SConstruction
