module
public import SerrePositivity.InfinityCategories.Kan.SimplexLastContraction

public import SerrePositivity.KST.Spectra.PointedHomotopy
public import Mathlib.AlgebraicTopology.SimplicialSet.Horn

/-!
概要：標準単体の最後の頂点への区間収縮。
方針：区間の零値では元の値を、一区間側では最後の頂点を取る単調写像を使う。
規約：最後のホーンも保つ。Kan 性やモデル構造を仮定しない。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.2。境界のホモトピー類による充填判定。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial

namespace SerrePositivity.KST.Spectra.SimplexLastContraction

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：標準単体の恒等射から最後の頂点への実際のホモトピー。
方針：切り替え写像と二つの端点の計算を束ねる。
規約：相対条件は空部分複体についてのみ。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.2。Kan fibration の底の収縮。 -/
def homotopy (n : ℕ) : SSet.Homotopy (𝟙 (Δ[n] : SSet.{u})) (SSet.const (_root_.SerrePositivity.InfinityCategories.Kan.SimplexLastContraction.vertex n)) where
  h := _root_.SerrePositivity.InfinityCategories.Kan.SimplexLastContraction.map n
  h₀ := _root_.SerrePositivity.InfinityCategories.Kan.SimplexLastContraction.zero n
  h₁ := _root_.SerrePositivity.InfinityCategories.Kan.SimplexLastContraction.one n
  rel := by ext m ⟨⟨x, hx⟩, t⟩; exact hx.elim

end SerrePositivity.KST.Spectra.SimplexLastContraction
