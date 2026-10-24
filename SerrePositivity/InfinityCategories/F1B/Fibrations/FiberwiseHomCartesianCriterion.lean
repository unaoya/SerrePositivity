module

public import SerrePositivity.InfinityCategories.F1B.Fibrations.FiberwiseHomLifting
public import SerrePositivity.InfinityCategories.F1.Fibrations.CartesianEdge

/-!
概要：相対指数の辺の cartesian 性を最後の外ホーンの逆像上の図式の延長で判定する。
方針：固定辺の条件を curry の下で保持し、持ち上げと図式の延長を往復する。
規約：射影の充填性や標的の quasicategory 性は判定そのものには不要。
使われ方：特殊な辺の可逆化条件から cartesian な持ち上げを構成する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：相対指数の辺は、対応する固定終端辺の図式が全て延長できることと同値に cartesian。
方針：最後の外ホーンの射を底を固定した Hom の全単射で図式へ戻す。
規約：終端辺の一致を厳密な一単体の等式として保持する。
使われ方：模型上の外ホーン充填を相対指数の cartesian 性へ渡す。 -/
lemma fiberwiseHom_isCartesianEdge_iff {K C D : SSet.{u}} (p : K ⟶ C)
    (e : (SerrePositivity.InfinityCategories.fiberwiseHom p D) _⦋1⦌) :
    IsCartesianEdge (SerrePositivity.InfinityCategories.fiberwiseHomProjection p D) e ↔
      ∀ (n : ℕ) (b : (Δ[n + 2] : SSet.{u}) ⟶ C)
        (H₀ : pullback ((horn (n + 2) (Fin.last (n + 2))).ι ≫ b) p ⟶ D),
        (SerrePositivity.InfinityCategories.fiberwiseHomCurry p _ H₀).app (Opposite.op ⦋1⦌) (finalHornEdge n) = e →
        ∃ H : pullback b p ⟶ D,
          (overPullbackUnderlying p).map
            (Over.homMk (horn (n + 2) (Fin.last (n + 2))).ι rfl :
              Over.mk ((horn (n + 2) (Fin.last (n + 2))).ι ≫ b) ⟶ Over.mk b) ≫ H = H₀ := by
  constructor
  · intro he n b H₀ h₀
    let a := SerrePositivity.InfinityCategories.fiberwiseHomCurry p ((horn (n + 2) (Fin.last (n + 2))).ι ≫ b) H₀
    let sq : CommSq a (horn (n + 2) (Fin.last (n + 2))).ι
        (SerrePositivity.InfinityCategories.fiberwiseHomProjection p D) b := ⟨SerrePositivity.InfinityCategories.fiberwiseHomCurry_projection p _ H₀⟩
    have := he n a b h₀ sq
    obtain ⟨H, hH⟩ := (SerrePositivity.InfinityCategories.fiberwiseHom_hasLift_iff p sq).1 (inferInstance : sq.HasLift)
    exact ⟨H, hH.trans ((SerrePositivity.InfinityCategories.fiberwiseHomEquiv (D := D) p _).symm_apply_apply H₀)⟩
  · intro h n a b ha sq
    let H₀ := (SerrePositivity.InfinityCategories.fiberwiseHomEquiv (D := D) p _).symm ⟨a, sq.w⟩
    have h₀ : SerrePositivity.InfinityCategories.fiberwiseHomCurry p _ H₀ = a :=
      congrArg Subtype.val ((SerrePositivity.InfinityCategories.fiberwiseHomEquiv (D := D) p _).apply_symm_apply ⟨a, sq.w⟩)
    exact (SerrePositivity.InfinityCategories.fiberwiseHom_hasLift_iff p sq).2 (h n b H₀ (by rw [h₀]; exact ha))

end SerrePositivity.InfinityCategories
