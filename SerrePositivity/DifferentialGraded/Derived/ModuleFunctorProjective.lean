module
public import SerrePositivity.DifferentialGraded.Derived.ProjectiveResolution

/-! # 任意dg加群関手は射影的加群間の準同型を保つ

## 概要
射影的対象間の準同型は主Kで同型であり、dg関手のH⁰関手とホモロジーがそれを保つ。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。固定dg圏上の導来tensor・Morita作用の基盤。
非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]

lemma dgModuleFunctor_projective_quasiIso
    (L : DGFunctor A (RightModule A D) (RightModule A E))
    {M N : ModuleCategory A D} (hM : moduleHomotopicallyProjective A D M)
    (hN : moduleHomotopicallyProjective A D N) (f : M ⟶ N) (hf : moduleQuasiIso A D f) :
    moduleQuasiIso A E (L.onClosed.map f) := by
  have : IsIso ((moduleToHomotopy A D).map f) :=
    moduleHomotopicallyProjective_quasiIso_isIso_homotopy A D hM hN f hf
  apply (moduleHomotopyQuasiIso_map_iff A E (L.onClosed.map f)).1
  rw [moduleHomotopyQuasiIso_iff]
  intro e i
  change IsIso ((moduleHomotopyHomology A E e i).map
    (L.onHomotopy.map ((moduleToHomotopy A D).map f)))
  infer_instance

end SerrePositivity.DifferentialGraded
