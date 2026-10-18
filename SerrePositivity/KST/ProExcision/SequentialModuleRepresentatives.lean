module
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# 順序余極限の加群の有限段階の代表と単射性

概要：実順序余極限の各元を有限段階で表し、有限段階の自己同型比較から単射性を導く。
方針：忘却関手の filtered colimit 保存と実余極限の全射性を使う。
規約：KST Proposition 4.14、SW92 Lemma 1.4 の加群部分。行列の置換比較は別に実証明する。
使われ方：安定相対零化と先頭単位座標の挿入のホモロジー単射性。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Limits

/-- 概要：実順序余極限の加群の各元は有限段階から来る。
方針：ModuleCat の忘却関手による余極限保存で型の余極限の全射性を使う。
規約：KST Proposition 4.14、SW92 Lemma 1.4。
使われ方：有限 rank の零化を安定 rank へ移す。 -/
lemma sequentialModule_representative (F : ℕ ⥤ ModuleCat.{u} ℤ) (c : Cocone F)
    (hc : IsColimit c) (x : c.pt) : ∃ n, ∃ v : F.obj n, (c.ι.app n).hom v = x := by
  have : PreservesFilteredColimitsOfSize.{0, 0} (forget AddCommGrpCat.{u}) :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits _
  let U := forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u} ⋙ forget AddCommGrpCat.{u}
  have : PreservesColimitsOfShape ℕ U := by dsimp only [U]; infer_instance
  exact Types.jointly_surjective_of_isColimit (isColimitOfPreserves U hc) x

/-- 概要：有限段階の全ての脚で零となる実順序余極限からの線形写像は零。
方針：実余極限の射の外延性を使う。
規約：KST Claim 4.15 から安定零化への加群部分。
使われ方：有限 rank の相対写像の零化の安定化。 -/
lemma sequentialModule_map_zero (F : ℕ ⥤ ModuleCat.{u} ℤ) (c : Cocone F)
    (hc : IsColimit c) {N : ModuleCat.{u} ℤ} (t : c.pt ⟶ N)
    (ht : ∀ n, c.ι.app n ≫ t = 0) : t = 0 := by
  apply hc.hom_ext
  intro n
  simpa only [Limits.comp_zero] using ht n

/-- 概要：各有限段階で自己同型と比較できる安定自己写像は単射。
方針：二元の差を有限段階で表し、比較先の自己同型の単射性を使う。
規約：SW92 Lemma 1.4 の加群部分。実置換共役の比較は入力として分離する。
使われ方：先頭に単位座標を入れる実安定写像の単射性への適用。 -/
lemma sequentialModule_map_injective_of_finite_iso (F : ℕ ⥤ ModuleCat.{u} ℤ) (c : Cocone F)
    (hc : IsColimit c) (t : c.pt ⟶ c.pt)
    (ht : ∀ n, ∃ e : c.pt ≅ c.pt, c.ι.app n ≫ t = c.ι.app n ≫ e.hom) :
    Function.Injective t.hom := by
  intro x y hxy
  obtain ⟨n, v, hv⟩ := sequentialModule_representative F c hc (x - y)
  obtain ⟨e, he⟩ := ht n
  have hz : t.hom (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  have hez : e.hom.hom (x - y) = 0 := by
    rw [← hv]
    calc
      e.hom.hom ((c.ι.app n).hom v) = t.hom ((c.ι.app n).hom v) :=
        (congrArg (fun f ↦ f.hom v) he).symm
      _ = 0 := by rw [hv]; exact hz
  have hinj : Function.Injective e.hom.hom := (ModuleCat.mono_iff_injective e.hom).mp inferInstance
  exact sub_eq_zero.mp (hinj (hez.trans (map_zero e.hom.hom).symm))

end SerrePositivity.KST.ProExcision
