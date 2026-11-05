module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.BridgePreservation
public import SerrePositivity.InfinityCategories.F2.Compact.CoconeLegEdge
/-!
概要：元の余錐の脚を、後合成・添字制限・宇宙持ち上げと厳密に照合する。
方針：同じ二点 join の一単体と Yoneda 表示を計算する。
規約：脚のホモトピー類ではなく全一単体を保持する。
使われ方：評価空間余錐の実脚へ元のホモロジー脚の自然性を適用する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet HomotopyLimits
open scoped _root_.Simplicial

lemma dgBarCompactCoconeLeg_map {K X Y : SSet.{u}} {p : K ⟶ X}
    (c : JoinCocone p) (q : X ⟶ Y) (i : (Δ[0] : SSet.{u}) ⟶ K) :
    ((mapJoinCocone q c).leg i).edge = q.app (Opposite.op ⦋1⦌) (c.leg i).edge := by
  change SSet.yonedaEquiv ((joinStdSimplexIso 0 0).inv ≫ joinMap i (𝟙 Δ[0]) ≫ (c.val ≫ q)) =
    q.app _ (SSet.yonedaEquiv ((joinStdSimplexIso 0 0).inv ≫ joinMap i (𝟙 Δ[0]) ≫ c.val))
  rw [← SSet.yonedaEquiv_comp]
  simp only [Category.assoc]

lemma dgBarCompactCoconeLeg_restrict {K L X : SSet.{u}} {p : K ⟶ X}
    (c : JoinCocone p) (f : L ⟶ K) (b : L _⦋0⦌) :
    ((c.restrict f).leg (SSet.yonedaEquiv.symm b)).edge =
      (c.leg (SSet.yonedaEquiv.symm (f.app _ b))).edge := by
  change SSet.yonedaEquiv ((joinStdSimplexIso 0 0).inv ≫
    joinMap (SSet.yonedaEquiv.symm b) (𝟙 Δ[0]) ≫ (joinMap f (𝟙 Δ[0]) ≫ c.val)) = _
  rw [← Category.assoc (joinMap _ _) (joinMap _ _), ← joinMap_comp,
    Category.id_comp, SSet.yonedaEquiv_symm_comp]
  rfl

lemma dgBarCompactCoconeLeg_ulift {K X : SSet.{u}} {p : K ⟶ X}
    (c : JoinCocone p) (b : K _⦋0⦌) :
    ((JoinCocone.ulift.{u, v} c).leg (SSet.yonedaEquiv.symm (ULift.up b))).edge =
      ULift.up (c.leg (SSet.yonedaEquiv.symm b)).edge := by
  rfl

end SerrePositivity.InfinityCategories
