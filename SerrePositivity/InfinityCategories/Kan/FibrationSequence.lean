module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Kan.FibrationBoundary
public import SerrePositivity.InfinityCategories.Kan.FibrationExactness
public import SerrePositivity.InfinityCategories.Kan.FibrationNaturality
public import SerrePositivity.InfinityCategories.Kan.FibrationMultiplication

/-!
概要：Kan fibration のホモトピー長完全列の公開入口。
方針：相対ホーンで構成した連結写像、準同型性、自然性、全次数の完全性をまとめる。
規約：正次数は群、零次数は基点付き集合。HT-KQ や引用公理は使わない。
使われ方：Kerodon Theorem 3.2.6.1、Goerss–Jardine I §§7–8。Ω スペクトルの長完全列。
-/

@[expose] public section

universe u
open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra
end SerrePositivity.KST.Spectra
namespace SerrePositivity.InfinityCategories.Kan
open SerrePositivity.KST.Spectra

/-- 概要：Kan fibration のホモトピー長完全列は全次数で完全である。
方針：fiber、全空間、底の各位置で、基点の逆像と直前の射の像の一致を証明済みの補題で示す。
規約：fiber と全空間の次数は零を含む。底では全正次数を扱い、連結射の零次数の標的は集合。
使われ方：Kerodon Theorem 3.2.6.1、Goerss–Jardine I §§7–8。L9b の長完全列。 -/
theorem fiberLongExact {E B : SSet.{u}} (p : E ⟶ B) [Fibration p]
    [KanComplex E] [KanComplex B] (e : E _⦋0⦌) :
    (∀ (n : ℕ) (a : KanHomotopy (KanFiber p (p.app _ e)) n (fiberPoint p e)),
      KanHomotopy.map n (fiberι p (p.app _ e)) (fiberι_point p e) a = KanHomotopy.point n ↔
        ∃ b : KanHomotopyGroup B n (p.app _ e), connecting p e n b = a) ∧
    (∀ (n : ℕ) (a : KanHomotopy E n e),
      KanHomotopy.map n p rfl a = KanHomotopy.point n ↔
        ∃ b : KanHomotopy (KanFiber p (p.app _ e)) n (fiberPoint p e),
          KanHomotopy.map n (fiberι p (p.app _ e)) (fiberι_point p e) b = a) ∧
    (∀ (n : ℕ) (a : KanHomotopyGroup B n (p.app _ e)),
      connecting p e n a = KanHomotopy.point n ↔
        ∃ b : KanHomotopyGroup E n e, KanHomotopyGroup.map p rfl b = a) :=
  ⟨fun n a ↦ exact_connecting_fiber_all p e n a,
    fun n a ↦ exact_fiber_total_all p e n a,
    fun n a ↦ exact_total_base_all p e n a⟩

/-- 概要：正次数の連結準同型の値は相対ホーンで構成した連結写像と一致する。
方針：群準同型の定義を読む。
規約：底の次数は n + 2、fiber の次数は n + 1。
使われ方：Kerodon §§3.2.5–3.2.6。長完全列の群の部分と集合の部分の接続。 -/
@[simp]
theorem connectingHom_apply {E B : SSet.{u}} (p : E ⟶ B) [Fibration p]
    [KanComplex E] [KanComplex B] (e : E _⦋0⦌) (n : ℕ)
    (a : KanHomotopyGroup B (n + 1) (p.app _ e)) :
    connectingHom p e n a = connecting p e (n + 1) a := rfl

end SerrePositivity.InfinityCategories.Kan

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.connectingHom_apply := _root_.SerrePositivity.InfinityCategories.Kan.connectingHom_apply

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.fiberLongExact := _root_.SerrePositivity.InfinityCategories.Kan.fiberLongExact
