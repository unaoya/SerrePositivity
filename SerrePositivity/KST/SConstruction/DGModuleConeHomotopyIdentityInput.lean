module
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConeArrowComp
public import SerrePositivity.DifferentialGraded.Module.ConeRotation

/-!
概要：始域の恒等比較を持つ元 cone square の指定入力を回収する。
方針：恒等前合成と閉射による後合成を元斉次合成で表示する。
規約：元の加群ホモトピーを保持する。
使われ方：元回転 cone 比較の全自然な入力と実入力の照合。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

/-- 概要：元恒等 square の入力は元左包含と元ホモトピーの後合成の和。
方針：豊穣恒等則と元閉射の後合成計算を使用する。
規約：指定ホモトピー元を変更しない。使われ方：同じ実 cone map の全比較。 -/
lemma dgModuleConeHomotopyIdentityInput {M N Q : ModuleCategory R D}
    (f : M ⟶ N) (g : M ⟶ Q) (r : N ⟶ Q)
    (h : ModuleHomotopy R D (f ≫ r) ((𝟙 M) ≫ g)) :
    moduleConeHomotopyInput R D f g (𝟙 M) r h =
      moduleConeInlElement R D g +
        compose R (x := ForgetEnrichment.to (Complex R) M)
          (y := ForgetEnrichment.to (Complex R) Q)
          (z := ForgetEnrichment.to (Complex R) (moduleCone R D g))
          (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) (moduleConeInr R D g))).val
          h.val (add_zero (-1)) := by
  dsimp only [moduleConeHomotopyInput]
  rw [eHomWhiskerRight_id]
  exact congrArg (fun t => moduleConeInlElement R D g + t)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHomPostcompose_apply R D (moduleConeInr R D g) h.val)
end SerrePositivity.KST.SConstruction
