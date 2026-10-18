module
public import SerrePositivity.InfinityCategories.Stable.LeftFibrationFiberTransport

/-! # 制限と厳密に可換な fiber 輸送の持ち上げ

概要：二段階の射影で、中間の fiber の輸送が与えられれば、制限と厳密に可換な全空間の輸送を選べる。
方針：中間の区間族を制限射の left fibration に持ち上げ、終端を fiber に戻す。
規約：最初に選んだ中間の輸送を変更しない。使われ方：枝の余錐と共通始点の輸送の整合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：中間の fiber の輸送は left fibration である制限射に沿って厳密に持ち上げられる。
方針：制限後の区間族を初期包含から持ち上げ、終端で fiber の包含後に可換性を確認する。
規約：q の充填性は不要で、r だけを left fibration とする。使われ方：二枝の共通始点での同時輸送。 -/
lemma exists_leftFibrationFiberTransport_lift {E D B : SSet.{u}}
    (p : E ⟶ B) (q : D ⟶ B) (r : E ⟶ D) [LeftFibration r]
    (hr : r ≫ q = p) {x y : B _⦋0⦌}
    (a : SSet.Truncated.Edge (X := (truncation 2).obj B) x y)
    (T : LeftFibrationFiberTransport q a) :
    ∃ S : LeftFibrationFiberTransport p a,
      S.h ≫ r = (vertexFiberMap p q r hr x ▷ (Δ[1] : SSet.{u})) ≫ T.h ∧
      S.map ≫ vertexFiberMap p q r hr y = vertexFiberMap p q r hr x ≫ T.map := by
  let rx := vertexFiberMap p q r hr x
  let ry := vertexFiberMap p q r hr y
  obtain ⟨R, hR₀, hRr⟩ := leftFibration_prism_lift r (vertexFiberι p x)
    ((rx ▷ (Δ[1] : SSet.{u})) ≫ T.h) (by
      rw [← Category.assoc, SSet.ι₀_comp, Category.assoc, T.h₀]
      exact vertexFiberMap_ι p q r hr x)
  have hRp : R ≫ p = snd (vertexFiber p x) (Δ[1] : SSet.{u}) ≫
      SSet.yonedaEquiv.symm a.edge := by
    calc
      _ = R ≫ r ≫ q := congrArg (fun z => R ≫ z) hr.symm
      _ = _ := by
        rw [← Category.assoc, hRr, Category.assoc, T.over, ← Category.assoc,
          whiskerRight_snd]
  have hT : (SSet.ι₁ ≫ R) ≫ p = SSet.const y := by
    rw [Category.assoc, hRp, stablePrism_edge_one]
  let S : LeftFibrationFiberTransport p a :=
    { map := vertexFiberLift p y (SSet.ι₁ ≫ R) hT
      h := R
      h₀ := hR₀
      h₁ := (vertexFiberLift_ι p y (SSet.ι₁ ≫ R) hT).symm
      over := hRp }
  refine ⟨S, hRr, ?_⟩
  apply vertexFiber_hom_ext q y
  change (S.map ≫ ry) ≫ vertexFiberι q y = (rx ≫ T.map) ≫ vertexFiberι q y
  rw [Category.assoc, vertexFiberMap_ι]
  rw [← Category.assoc, ← S.h₁, Category.assoc, hRr]
  rw [← Category.assoc, SSet.ι₁_comp, Category.assoc, T.h₁, Category.assoc]

end SerrePositivity.InfinityCategories
