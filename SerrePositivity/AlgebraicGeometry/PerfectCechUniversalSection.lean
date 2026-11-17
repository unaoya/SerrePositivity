module

public import SerrePositivity.AlgebraicGeometry.SectionPerfectCechTupleTotal

/-!
概要：切断を持つ射に完全構造層の普遍Čech降下を供給する。
方針：元の切断を各アフィン試験基底へpullbackし、同じ被覆へF07を適用する。
規約：元の有限表示・準コンパクト・分離性と全ての試験被覆を保持する。
使われ方：相対fppfの正次数の軸（承認済み計画D05）。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
set_option backward.isDefEq.respectTransparency false

/-- 元の切断を各試験基底へ底変換して、普遍Čech降下を得る。 -/
theorem perfectCechUniversalDescent_of_section
    (p : ℕ) (hp : p.Prime) {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsSeparated f] [QuasiCompact f] [LocallyOfFinitePresentation f]
    (s : Y ⟶ X) (hs : s ≫ f = 𝟙 _) : PerfectCechUniversalDescent p hp f := by
  intro R _ _ hR t ι _ _ U hU hcU
  let r : Spec (CommRingCat.of R) ⟶ pullback f t :=
    pullback.lift (t ≫ s) (𝟙 _) (by rw [Category.assoc, hs, Category.comp_id, Category.id_comp])
  exact section_perfectCechTupleTotal_acyclic (pullback.snd f t) r
    (pullback.lift_snd _ _ _) p hp hR U hU hcU

end SerrePositivity.AlgebraicGeometry
