module

public import SerrePositivity.KST.Spectra.CotensorLoopGroups

/-!
概要：Ω スペクトルの零段を落とす関手と整数次数群の添字移動。
方針：各段と構造射を一つ先へずらし、任意段表示の同型を合成する。
規約：∞ 圏での suspension との同定は主張しない。
使われ方：BF 1978 §2、HA §1.4.2。有理化の loop 模型の次数調整。
-/

@[expose] public section

universe u

open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra.OmegaSpectrum

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：Ω スペクトルの各段を一つ先にずらした BF 対象。
方針：一段先の構造射と元の証明を使う。
規約：零段を落とす操作。
使われ方：BF 1978 §2、HA §1.4.2。整数次数の移動。 -/
def tail (X : OmegaSpectrum.{u}) : OmegaSpectrum.{u} where
  level n := X.level (n + 1)
  sigma n := X.sigma (n + 1)
  sigma_mono n := X.sigma_mono (n + 1)
  omega_condition n := X.omega_condition (n + 1)

/-- 概要：スペクトルの射の各段も一つ先にずらす。
方針：元の一段先の成分と構造可換式を使う。
規約：通常の厳密なスペクトルの射。
使われ方：BF 1978 §2。tail の関手性。 -/
def tailMap {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) : tail X ⟶ tail Y where
  app n := f.app (n + 1)
  comm n := f.comm (n + 1)

/-- 概要：零段を落とす通常の関手。
方針：段の再添字づけの恒等・合成法則を使う。
規約：BF 対象の厳密な圏の関手。
使われ方：BF 1978 §2、HA §1.4.2。telescope 図式の次数調整。 -/
def tailFunctor : OmegaSpectrum.{u} ⥤ OmegaSpectrum.{u} where
  obj := tail
  map := tailMap
  map_id _ := rfl
  map_comp _ _ := rfl

/-- 概要：整数次数を一つ下げて段を一つ上げると計算次数は同じ。
方針：整数の和の等式を自然数部分へ移す。
規約：許容段の条件はこの算術等式には不要。
使われ方：BF 1978 §2。tail のホモトピー群の比較。 -/
theorem degree_tail (j : ℤ) (k : ℕ) : degree (j - 1) (k + 1) = degree j k := by
  unfold degree
  congr 1
  omega

/-- 概要：零段を落とすと整数次数の群が一つ下がる。
方針：tail の k 段と元の k+1 段の同一の群を任意段表示で比較する。
規約：全整数次数で π_j(tail X)≃π_{j-1}(X)。
使われ方：BF 1978 §2、HA §1.4.2。loop と tail の次数の相殺。 -/
def tailHomotopyEquiv (X : OmegaSpectrum.{u}) (j : ℤ) :
    homotopyGroup (tail X) j ≃* homotopyGroup X (j - 1) := by
  have hk : -(j - 1) ≤ ((boundaryStage j + 1 : ℕ) : ℤ) := by
    have h := boundaryStage_admissible j
    omega
  have hd : degree (j - 1) (boundaryStage j + 1) = boundaryIndex j + 1 :=
    (degree_tail j (boundaryStage j)).trans (boundaryStage_degree j)
  exact (positiveStageEquiv (tail X) j (boundaryStage j) (boundaryIndex j)
    (boundaryStage_admissible j) (boundaryStage_degree j)).trans
      (positiveStageEquiv X (j - 1) (boundaryStage j + 1) (boundaryIndex j) hk hd).symm

/-- 概要：円の cotensor の後で零段を落とすと元と同じ整数次数群を得る。
方針：二つの次数移動の同型を合成し、整数の減算と加算を相殺する。
規約：対象間の厳密な同型や射はこの群の同型から主張しない。
使われ方：BF 1978 §2、HA §1.4.2。有理化用の loop 模型の群の表示。 -/
def tailCotensorLoopHomotopyEquiv (X : OmegaSpectrum.{u}) (j : ℤ) :
    homotopyGroup (tail (cotensor PointedSimplicialSet.circle.{u} X)) j ≃*
      homotopyGroup X j :=
  (tailHomotopyEquiv (cotensor PointedSimplicialSet.circle.{u} X) j).trans
    ((cotensorLoopHomotopyEquiv X (j - 1)).trans
      (by rw [sub_add_cancel]))

end

end SerrePositivity.KST.Spectra.OmegaSpectrum
