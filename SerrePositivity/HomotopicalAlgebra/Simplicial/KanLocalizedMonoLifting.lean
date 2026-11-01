module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanMonoRelativeHomotopy
public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanMonoStrictExtension
public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanFibrationEndpointExtension

/-!
# 局所化で可逆な単射はKan基底上のKan fibrationに対して持ち上げ性を持つ

## 概要
局所化で可逆な単射はKan基底上のKan fibrationに対して持ち上げ性を持つ。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
構成に現れる射と比較写像を明示し、各成分の等式を照合する。
既存の普遍性と自然性、必要な帰納を用いて全体の主張へ接続する。

## 規約と注意
Kan条件・右持ち上げ性・単射性は各宣言で指定された範囲で用いる。
ここでのKan条件は外側も含む全hornの充填であり、内側hornだけの条件ではない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。
[棚卸し m0419][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/k-theory-generalization-inventory.md#m0419
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Localized mono equivalences lift against Kan fibrations with Kan base

The extension and both endpoint corrections retain the original square.
No model structure or additional weak-equivalence class is assumed.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace SerrePositivity.SimplicialModel.KanLocalizedMonoLifting
variable {A T E B : SSet.{v}} (i : A ⟶ T) [Mono i]
  (hi : IsIso (AnodyneHomotopy.anodyneQ.map i))
  (p : E ⟶ B) (hp : SSet.modelCategoryQuillen.J.rlp p)
  (hB : SSet.modelCategoryQuillen.J.rlp (terminal.from B))

include hi hp hB in
/-- 局所化で可逆な単射はKan基底上のKan fibrationに対して持ち上げ性を持つ。

Kan条件・右持ち上げ性・単射性は各宣言で指定された範囲で用いる。
構成に現れる射と比較写像を明示し、各成分の等式を照合する。
既存の普遍性と自然性、必要な帰納を用いて全体の主張へ接続する。
-/
lemma hasLiftingProperty : HasLiftingProperty i p := by
  have : Fibration p := (SSet.modelCategoryQuillen.fibration_iff _).mpr hp
  have : Fibration (terminal.from B) := (SSet.modelCategoryQuillen.fibration_iff _).mpr hB
  have : SSet.KanComplex B := (isFibrant_iff B).mpr inferInstance
  have : SSet.KanComplex E := isFibrant_of_fibration p
  have hE : SSet.modelCategoryQuillen.J.rlp (terminal.from E) :=
    (SSet.modelCategoryQuillen.fibration_iff _).mp inferInstance
  constructor
  intro a b sq
  obtain ⟨g, hg⟩ := KanMonoStrictExtension.exists_extension i hE hi a
  let H₀ : SSet.Homotopy (i ≫ (g ≫ p)) (i ≫ b) :=
    { h := fst A (SSet.stdSimplex.obj (SimplexCategory.mk 1)) ≫ a ≫ p
      h₀ := by
        rw [← Category.assoc, AnodyneHomotopy.endpoint_projection_zero, Category.id_comp]
        exact (congrArg (fun f => f ≫ p) hg).symm.trans (Category.assoc _ _ _)
      h₁ := by
        rw [← Category.assoc, AnodyneHomotopy.endpoint_projection_one, Category.id_comp]
        exact sq.w
      rel := by
        apply NatTrans.ext
        funext n
        exact ConcreteCategory.hom_ext _ _ (fun x => False.elim x.1.property) }
  obtain ⟨H, hH⟩ := KanMonoRelativeHomotopy.exists_extension i hi hB (g ≫ p) b H₀
  let Ha : SSet.Homotopy (i ≫ g) a :=
    { h := fst A (SSet.stdSimplex.obj (SimplexCategory.mk 1)) ≫ a
      h₀ := by
        rw [← Category.assoc, AnodyneHomotopy.endpoint_projection_zero, Category.id_comp]
        exact hg.symm
      h₁ := by
        rw [← Category.assoc, AnodyneHomotopy.endpoint_projection_one, Category.id_comp]
        rfl
      rel := by
        apply NatTrans.ext
        funext n
        exact ConcreteCategory.hom_ext _ _ (fun x => False.elim x.1.property) }
  have hHa : Ha.h ≫ p = i ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫ H.h := by
    rw [hH]
    rfl
  obtain ⟨g', hg', ⟨V, _, hVp⟩⟩ := KanFibrationEndpointExtension.exists_from_zero p hp i g a Ha
    H.h H.h₀.symm hHa
  refine CommSq.HasLift.mk' { l := g', fac_left := hg', fac_right := ?_ }
  calc
    g' ≫ p = (SSet.ι₁ ≫ V.h) ≫ p := congrArg (fun f => f ≫ p) V.h₁.symm
    _ = SSet.ι₁ ≫ (V.h ≫ p) := Category.assoc _ _ _
    _ = SSet.ι₁ ≫ H.h := congrArg (fun f => SSet.ι₁ ≫ f) hVp
    _ = b := H.h₁

end SerrePositivity.SimplicialModel.KanLocalizedMonoLifting
