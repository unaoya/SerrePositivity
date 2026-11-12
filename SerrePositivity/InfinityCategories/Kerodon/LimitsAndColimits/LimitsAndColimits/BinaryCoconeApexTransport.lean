module

public import SerrePositivity.InfinityCategories.Stable.BinaryCoconeEdgeLift
public import SerrePositivity.InfinityCategories.Core.InitialTransport

/-!
# 二点離散図式の余錐の頂点同値による移送

概要：Kerodon §7.1 の余極限について、頂点の同値と二脚のホモトピー圏での
可換式から、指定された二点図式の余錐全体の同値を得る。
方針：二脚の可換式を合成二単体へ持ち上げ、coslice の辺を作る。
頂点射影は左ファイブレーションなので、その辺の可逆性を反映する。
規約：安定性・模型・テンソル構造は仮定しない。図式と二つの余錐を固定する。
使われ方：D78、BS のテンソル比較から指定余積錐を移す一般補題。

KL-W1 後の置き場所での未検証下書き。import と既存の宣言名は、
取り込み後に配布される改名表で追従してから検証する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open CategoryTheory Limits SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 二脚と可換な頂点の同値は、同じ二点図式上の余錐全体の同値へ持ち上がる。 -/
lemma binaryCoconeVertexIso_of_apexIso {X : SSet.{u}} [Quasicategory X]
    {p : (Δ[0] : SSet.{u}) ⨿ Δ[0] ⟶ X} (c d : JoinCocone p)
    (e : VertexIso c.vertex d.vertex)
    (hL : Truncated.HomotopyCategory.homMk (c.leg binaryPointLeft) ≫ e.hom =
      Truncated.HomotopyCategory.homMk (d.leg binaryPointLeft))
    (hR : Truncated.HomotopyCategory.homMk (c.leg binaryPointRight) ≫ e.hom =
      Truncated.HomotopyCategory.homMk (d.leg binaryPointRight)) :
    Nonempty (VertexIso (X := sliceUnder p) c d) := by
  obtain ⟨a, ha⟩ := homotopyCategory_homMk_surjective c.vertex d.vertex e.hom
  have hai : IsInvertibleEdge (X := X) a := by
    rw [IsInvertibleEdge, ha]
    infer_instance
  obtain ⟨b, hb⟩ := exists_binaryCoconeEdgeLift_of_comm a
    (by simpa only [ha] using hL) (by simpa only [ha] using hR)
  have hbi : IsInvertibleEdge (X := sliceUnder p) b :=
    leftFibration_reflects_invertibleEdge (sliceUnderProjection p) b
      ((isInvertibleEdge_congr hb).mpr hai)
  exact ⟨asIso (Truncated.HomotopyCategory.homMk b)⟩

/-- 頂点同値で二脚がホモトピー圏で一致すれば、指定余錐の余極限性は同値。 -/
lemma isColimitCone_iff_binaryCocone_apexIso {X : SSet.{u}} [Quasicategory X]
    {p : (Δ[0] : SSet.{u}) ⨿ Δ[0] ⟶ X} (c d : JoinCocone p)
    (e : VertexIso c.vertex d.vertex)
    (hL : Truncated.HomotopyCategory.homMk (c.leg binaryPointLeft) ≫ e.hom =
      Truncated.HomotopyCategory.homMk (d.leg binaryPointLeft))
    (hR : Truncated.HomotopyCategory.homMk (c.leg binaryPointRight) ≫ e.hom =
      Truncated.HomotopyCategory.homMk (d.leg binaryPointRight)) :
    IsColimitCone c ↔ IsColimitCone d := by
  obtain ⟨h⟩ := binaryCoconeVertexIso_of_apexIso c d e hL hR
  exact isColimitCone_iff_of_vertexIso h

/-- 二点離散図式の指定余極限錐を、二脚と可換な頂点同値で移送する。 -/
lemma IsColimitCone.of_binaryCocone_apexIso {X : SSet.{u}} [Quasicategory X]
    {p : (Δ[0] : SSet.{u}) ⨿ Δ[0] ⟶ X} {c d : JoinCocone p}
    (hc : IsColimitCone c) (e : VertexIso c.vertex d.vertex)
    (hL : Truncated.HomotopyCategory.homMk (c.leg binaryPointLeft) ≫ e.hom =
      Truncated.HomotopyCategory.homMk (d.leg binaryPointLeft))
    (hR : Truncated.HomotopyCategory.homMk (c.leg binaryPointRight) ≫ e.hom =
      Truncated.HomotopyCategory.homMk (d.leg binaryPointRight)) :
    IsColimitCone d :=
  (isColimitCone_iff_binaryCocone_apexIso c d e hL hR).mp hc

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
