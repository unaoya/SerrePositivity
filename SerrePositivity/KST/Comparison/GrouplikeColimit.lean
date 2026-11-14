module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.KST.Comparison.MonoidComponentMaps
public import Mathlib.Algebra.Category.MonCat.FilteredColimits
public import Mathlib.Algebra.Category.MonCat.Colimits

/-!
# 群状単体的モノイドの順序余極限

概要：群状単体的モノイドの順序列の実際の余極限は群状である。
方針：零単体を有限段階から持ち上げ、成分の単元性を自然なモノイド射で移す。
規約：KST 式 (2.3)、Lemma 2.13 の安定 rank の群状性。
使われ方：安定 ĜL の群完備化の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits Opposite SSet
open scoped Simplicial

/--
概要：群状単体的モノイドの順序列の余極限は群状である。
方針：零次評価と忘却関手の filtered colimit 保存で有限段階の代表を取り、成分の単元を移す。
規約：遷移の単射性や各単体次数の群性は不要。
使われ方：安定 rank の ĜL の群状性。
-/
theorem isGrouplike_of_sequential_isColimit
    {F : ℕ ⥤ SimplicialObject MonCat.{u}} {c : Cocone F} (hc : IsColimit c)
    (hF : ∀ n, SimplicialMonoid.IsGrouplike (F.obj n)) :
    SimplicialMonoid.IsGrouplike c.pt := by
  have : PreservesFilteredColimitsOfSize.{0, 0} (forget MonCat.{u}) :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits _
  let U := (evaluation SimplexCategoryᵒᵖ MonCat.{u}).obj (op ⦋0⦌) ⋙ forget MonCat
  have : PreservesColimitsOfShape ℕ U := by
    dsimp only [U]
    infer_instance
  have hc₀ := isColimitOfPreserves U hc
  let := SimplicialMonoid.componentsMonoid c.pt
  intro a
  induction a using π₀.rec with | mk a => ?_
  obtain ⟨n, x, hx⟩ := Types.jointly_surjective_of_isColimit hc₀ a
  change ((c.ι.app n).app (op ⦋0⦌)) x = a at hx
  let := SimplicialMonoid.componentsMonoid (F.obj n)
  rw [← hx]
  exact (hF n (π₀.mk x)).map (SimplicialMonoid.componentsMap (M := F.obj n) (N := c.pt) (c.ι.app n))

end SerrePositivity.KST.Comparison

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "5.2.6.9" (partial := component) "仮定：厳密単体的モノイドの自然数順序列の実際の余極限で各項の π₀ が群（Lean が強い：k=1 の厳密模型の順序列）。結論：余極限も π₀ が群で、成分モノイド関手は定数関手の左随伴となる（順序列での閉性と π₀ の余極限保存の通常模型の部分）。全 k の空間の ∞ 余極限との比較と任意小余極限の閉性は含まれない。"] _root_.SerrePositivity.KST.Comparison.isGrouplike_of_sequential_isColimit
