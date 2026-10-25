module

public import SerrePositivity.InfinityCategories.F2.Presentable.CompactEquivalence
public import SerrePositivity.InfinityCategories.F2.Compact.Subcategory
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FullSubcomplexRestrictionEquivalence
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FullSubcomplexEquivalenceLifting

/-!
概要：compact 対象を保つ元の関手を、全 compact 全部分圏の間の関手へ制限する。
方針：全部分複体の公開 API で元の射・同値・同値持ち上げ性を制限する。
規約：元の全辺・高次単体を保持し、compact 保存条件を明示する。
使われ方：引き戻しの compact な成分圏を小さい模型へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：元の compact 保存関手の全 compact 全部分圏への制限。
方針：元の包含との合成を頂点条件により持ち上げる。
規約：元の射への包含との可換性を厳密に保つ。
使われ方：小さい compact 成分図式を構成する。 -/
def kappaCompactRestriction (κ : Cardinal.{u})
    {C D : SSet.{u + 1}} [Quasicategory C] [Quasicategory D]
    (G : C ⟶ D) (hG : ∀ x : C _⦋0⦌, Compact.IsKappaCompact.{u, u + 1} κ x →
      Compact.IsKappaCompact.{u, u + 1} κ (G.app _ x)) :
    Compact.kappaCompactObjects.{u, u + 1} κ C ⟶ Compact.kappaCompactObjects.{u, u + 1} κ D :=
  fullSubcomplexLift (Compact.IsKappaCompact.{u, u + 1} κ)
    (Compact.kappaCompactInclusion.{u, u + 1} κ C ≫ G)
    (fun x ↦ hG x.val (fullSubcomplexOnVertices_vertex x))

/-- 概要：compact 制限は元の関手への包含を保つ。
方針：全部分複体への持ち上げの包含公式を使う。
規約：全パラメーターの射の等式。
使われ方：制限した図式の元の圏への回収。 -/
lemma kappaCompactRestriction_inclusion (κ : Cardinal.{u})
    {C D : SSet.{u + 1}} [Quasicategory C] [Quasicategory D]
    (G : C ⟶ D) (hG : ∀ x : C _⦋0⦌, Compact.IsKappaCompact.{u, u + 1} κ x →
      Compact.IsKappaCompact.{u, u + 1} κ (G.app _ x)) :
    kappaCompactRestriction κ G hG ≫ Compact.kappaCompactInclusion.{u, u + 1} κ D =
      Compact.kappaCompactInclusion.{u, u + 1} κ C ≫ G := rfl

/-- 概要：元の全同値は全 compact 全部分圏の全同値を誘導する。
方針：compact 不変性と、同型不変な頂点条件への全同値の制限を使う。
規約：元の順方向の関手を制限したものに固定する。
使われ方：具体的な Ind 模型の compact 小模型を元の圏へ移す。 -/
def kappaCompactEquivalence (κ : Cardinal.{u})
    {C D : SSet.{u + 1}} [Quasicategory C] [Quasicategory D]
    (e : QCatEquivalence C D) :
    QCatEquivalence (Compact.kappaCompactObjects.{u, u + 1} κ C)
      (Compact.kappaCompactObjects.{u, u + 1} κ D) := by
  let r := kappaCompactRestriction κ e.hom (fun x hx ↦
    (isKappaCompact_iff_equivalence e x).mp hx)
  exact (isQCatEquivalence_fullSubcomplexRestriction
    (Compact.IsKappaCompact.{u, u + 1} κ) (Compact.IsKappaCompact.{u, u + 1} κ)
    (fun e ↦ Compact.isKappaCompact_iff_of_iso e) e.hom e.isQCatEquivalence r
    (kappaCompactRestriction_inclusion κ e.hom _) (fun x hx ↦
      (isKappaCompact_iff_equivalence e x).mpr hx)).choose

/-- 概要：元の同値持ち上げ性は compact 制限にも移る。
方針：compact 条件の頂点同型不変性と全部分制限の持ち上げ定理を使う。
規約：元の関手の同値持ち上げ性と compact 保存だけを要求する。
使われ方：compact な成分圏の引き戻しを元の引き戻しの全部分圏として扱う。 -/
lemma kappaCompactRestriction_equivalenceLifting (κ : Cardinal.{u})
    {C D : SSet.{u + 1}} [Quasicategory C] [Quasicategory D]
    (G : C ⟶ D) (hG : ∀ x : C _⦋0⦌, Compact.IsKappaCompact.{u, u + 1} κ x →
      Compact.IsKappaCompact.{u, u + 1} κ (G.app _ x)) (hp : F1B.EquivalenceLifting G) :
    F1B.EquivalenceLifting (kappaCompactRestriction κ G hG) :=
  kanEquivalenceLifting_fullRestriction (Compact.IsKappaCompact.{u, u + 1} κ)
    (fun e ↦ Compact.isKappaCompact_iff_of_iso e) (Compact.IsKappaCompact.{u, u + 1} κ)
    _ G (kappaCompactRestriction_inclusion κ G hG) hp

end SerrePositivity.InfinityCategories.F2.Presentable
