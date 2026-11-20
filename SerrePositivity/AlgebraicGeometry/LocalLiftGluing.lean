module

public import SerrePositivity.AlgebraicGeometry.SeparatedExt

/-!
概要：KST §5 の局所的な blowup 普遍写像の貼り合わせに使う一意性。
方針：片側の開集合上の零核の検出射を重なりへ引き戻す。
規約：位相的な稠密性でなくスキーム論的な核を使う。
使われ方：正則な単項中心からの持ち上げと共通細分の局所射の一致。
-/

@[expose] public noncomputable section

universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits

set_option backward.isDefEq.respectTransparency false in
/--
概要：局所的に中心外を検出する零核の射があれば、基底上の局所射は重なりで一致する。
方針：零核を開基底変換し、中心外での同型と分離性を順に使う。
規約：KST §5、開埋め込みは重なりの片側にだけ必要。
使われ方：基本開被覆に沿った正則な中心の普遍写像の貼り合わせ。
-/
theorem local_lift_overlap_hom_ext {A C T Y B W : Scheme.{u}}
    (s : Y ⟶ B) [IsSeparated s] (U : B.Opens) [IsIso (s ∣_ U)]
    (j : A ⟶ T) (k : C ⟶ T) [IsOpenImmersion k]
    (f : A ⟶ Y) (g : C ⟶ Y)
    (hbase : (pullback.fst j k ≫ f) ≫ s = (pullback.snd j k ≫ g) ≫ s)
    (q : W ⟶ A) [QuasiCompact q] (hq : q.ker = ⊥)
    (hU : Set.range (q ≫ f ≫ s) ⊆ U) :
    pullback.fst j k ≫ f = pullback.snd j k ≫ g := by
  let d := pullback.snd q (pullback.fst j k)
  apply hom_ext_of_ker_eq_bot_of_separated s hbase d
    (pullback_snd_ker_eq_bot_of_openImmersion q hq (pullback.fst j k))
  apply hom_ext_of_isIso_restrict s U
  · simp only [Category.assoc]
    exact congrArg (d ≫ ·) hbase
  · rw [← Category.assoc, ← pullback.condition, Category.assoc]
    rintro _ ⟨x, rfl⟩
    exact hU ⟨(pullback.fst q (pullback.fst j k)) x, rfl⟩

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
