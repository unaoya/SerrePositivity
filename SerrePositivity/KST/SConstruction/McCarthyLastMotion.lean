module
public import SerrePositivity.KST.SConstruction.OrderPrism
public import SerrePositivity.KST.SConstruction.ObjectSConstantRestriction

/-! # McCarthy の μ の添字と Ar 上の変換
概要：添字 α を時刻の切れ目から最後の頂点に動かし、Ar の元の添字からの変換を作る。
方針：標準単体の最後の頂点への収縮を順序写像に適用する。
規約：時刻は第一因子。使われ方：Fiore–Pieper (1.26)・(4.26) の λ→μ。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：時刻零では元の添字、時刻一では最後の頂点を取る動かした添字。
方針：最後の頂点への収縮の順序写像に時刻と元の添字を合わせる。
規約：α と τ は同じ有限鎖を始域とする。使われ方：μ の Ar 図式の添字。 -/
def mcCarthyMovedOrder {n m : ℕ} (α : Fin (n + 1) →o Fin (m + 1))
    (τ : Fin (n + 1) →o Fin 2) : Fin (n + 1) →o Fin (m + 1) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.prismLastOrderHom m).comp (τ.prod α)

/-- 概要：動かした添字は元の添字以上。
方針：時刻零は等号、時刻一は最後の頂点への不等式。
規約：各頂点での順序。使われ方：Ar の自然変換を作る順序条件。 -/
lemma mcCarthyMovedOrder_le {n m : ℕ} (α : Fin (n + 1) →o Fin (m + 1))
    (τ : Fin (n + 1) →o Fin 2) (i : Fin (n + 1)) : α i ≤ mcCarthyMovedOrder α τ i := by
  change α i ≤ if τ i = 0 then α i else Fin.last m
  split_ifs
  · rfl
  · exact Fin.le_last _

/-- 概要：動かした添字は全ての面・退化による前合成と可換。
方針：順序写像の合成を計算する。
規約：σ は任意の単調写像。使われ方：μ の単体恒等式。 -/
lemma mcCarthyMovedOrder_comp {l n m : ℕ} (α : Fin (n + 1) →o Fin (m + 1))
    (τ : Fin (n + 1) →o Fin 2) (σ : Fin (l + 1) →o Fin (n + 1)) :
    mcCarthyMovedOrder (α.comp σ) (τ.comp σ) = (mcCarthyMovedOrder α τ).comp σ := rfl

/-- 概要：零時刻の単体では添字は元のまま。
方針：各頂点の時刻零の分岐を計算する。
規約：全ての n,m。使われ方：ρ の恒等射側の端点。 -/
lemma mcCarthyMovedOrder_zero {n m : ℕ} (α : Fin (n + 1) →o Fin (m + 1)) :
    mcCarthyMovedOrder α (OrderHom.const _ 0) = α := by
  ext i
  rfl

/-- 概要：一時刻の単体では添字は最後の頂点に一定。
方針：各頂点の時刻一の分岐を計算する。
規約：全ての n,m。使われ方：ρ の零側の端点。 -/
lemma mcCarthyMovedOrder_one {n m : ℕ} (α : Fin (n + 1) →o Fin (m + 1)) :
    mcCarthyMovedOrder α (OrderHom.const _ 1) = OrderHom.const _ (Fin.last m) := by
  ext i
  rfl

/-- 概要：μ の添字の単体は標準単体の最後の頂点への実際の収縮で得られる。
方針：標準単体の各頂点で順序写像の合成を計算する。
規約：時刻の切れ目を持つ全ての単体を含む。使われ方：左 fiber のパラメーターの変換。 -/
lemma mcCarthyMovedOrder_simplex {n m : ℕ} (α : (Δ[m] : SSet.{u}) _⦋n⦌)
    (τ : (Δ[1] : SSet.{u}) _⦋n⦌) :
    stdSimplex.objEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.prismLastContraction m).app (Opposite.op ⦋n⦌) (τ, α)) =
      SimplexCategory.mkHom (mcCarthyMovedOrder (stdSimplex.objEquiv α).toOrderHom
        (stdSimplex.objEquiv τ).toOrderHom) := rfl

/-- 概要：元の Ar 添字から μ の Ar 添字への実際の prism。
方針：各区間の両端の順序 α≤μ を nerve の prism にする。
規約：標的 Ar[m] での coherent な変換。使われ方：λ→μ の正方形図式の上辺。 -/
def mcCarthyArMotion {n m : ℕ} (α : Fin (n + 1) →o Fin (m + 1))
    (τ : Fin (n + 1) →o Fin 2) : (Δ[1] : SSet.{u}) ⊗ arNerve n ⟶ arNerve m :=
  orderPrism (arMap α) (arMap (mcCarthyMovedOrder α τ))
    (fun a => ⟨mcCarthyMovedOrder_le α τ a.down.val.1,
      mcCarthyMovedOrder_le α τ a.down.val.2⟩)

/-- 概要：Ar の変換の始点は元の添字 α の制限。
方針：順序 prism の始点公式。
規約：射の厳密な等号。使われ方：λ の上辺。 -/
lemma mcCarthyArMotion_zero {n m : ℕ} (α : Fin (n + 1) →o Fin (m + 1))
    (τ : Fin (n + 1) →o Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (arNerve n) ≫ mcCarthyArMotion.{u} α τ = arNerveMap α :=
  orderPrism_zero _ _ _

/-- 概要：Ar の変換の終点は動かした添字 μ の制限。
方針：順序 prism の終点公式。
規約：射の厳密な等号。使われ方：μ の上辺。 -/
lemma mcCarthyArMotion_one {n m : ℕ} (α : Fin (n + 1) →o Fin (m + 1))
    (τ : Fin (n + 1) →o Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (arNerve n) ≫ mcCarthyArMotion.{u} α τ =
      arNerveMap (mcCarthyMovedOrder α τ) := orderPrism_one _ _ _

/-- 概要：Ar の変換は元の添字と時刻の面・退化の前合成と可換。
方針：順序 prism の前合成公式と Ar の関手法則。
規約：二つの端点だけでなく prism 全体の厳密な等号。使われ方：ρ の単体的自然性。 -/
lemma mcCarthyArMotion_pre {l n m : ℕ} (α : Fin (n + 1) →o Fin (m + 1))
    (τ : Fin (n + 1) →o Fin 2) (σ : Fin (l + 1) →o Fin (n + 1)) :
    (Δ[1] ◁ arNerveMap σ) ≫ mcCarthyArMotion.{u} α τ =
      mcCarthyArMotion (α.comp σ) (τ.comp σ) := by
  exact orderPrism_pre (arMap α) (arMap (mcCarthyMovedOrder α τ))
    (fun a => ⟨mcCarthyMovedOrder_le α τ a.down.val.1,
      mcCarthyMovedOrder_le α τ a.down.val.2⟩) (arMap σ)

/-- 概要：動かす時刻が全て零なら Ar の変換は元の添字で一定。
方針：動かした順序が元の順序に等しいことと定値 prism の式。
規約：prism 全体の厳密な等号。使われ方：恒等な上辺の押し出しの正規化。 -/
lemma mcCarthyArMotion_timeZero {n m : ℕ} (α : Fin (n + 1) →o Fin (m + 1)) :
    mcCarthyArMotion.{u} α (OrderHom.const _ 0) =
      CartesianMonoidalCategory.snd (Δ[1] : SSet.{u}) (arNerve n) ≫ arNerveMap α := by
  exact orderPrism_of_eq _ _ _ (congrArg arMap (mcCarthyMovedOrder_zero α))

end SerrePositivity.KST.SConstruction
