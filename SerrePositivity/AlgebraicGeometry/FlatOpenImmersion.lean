module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import SerrePositivity.AlgebraicGeometry.SeparatedExt

/-!
概要：Stacks 081S の平坦化後の射を開埋め込みと判定する段階。
方針：スキーム論的に稠密な開部分上で対角が同型となることを平坦基底変更で検出する。
規約：平坦化の存在を仮定の構造体へ移さず、既に平坦な射に対する幾何学的判定を証明する。
使われ方：Stacks 081T、Temkin 2008 Lemma 2.1.5 の Noether 特殊形。
-/

@[expose] public noncomputable section

universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits

set_option backward.isDefEq.respectTransparency false in
/--
概要：平坦・有限表示・分離な射がスキーム論的に稠密な開部分上で同型なら開埋め込み。
方針：対角の閉包含の核を稠密開部分の平坦基底変更で消し、平坦な単射の開埋め込み性を使う。
規約：Stacks 081S Lemma 38.31.3、38.11.5 の判定段階。稠密性はスキーム論的に仮定する。
使われ方：strict transform の平坦化の結論を開埋め込みへ移す。
-/
theorem isOpenImmersion_of_flat_iso_on_dense_open {X S : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [LocallyOfFinitePresentation f] [IsSeparated f]
    (U : S.Opens) [QuasiCompact U.ι] [IsSchemeTheoreticallyDominant U.ι]
    [IsIso (f ∣_ U)] : IsOpenImmersion f := by
  let h := pullback.fst f f ≫ f
  let d := pullback.snd U.ι h
  have : Flat h := by dsimp only [h]; infer_instance
  have : IsSchemeTheoreticallyDominant d := by dsimp only [d]; infer_instance
  have heq : d ≫ pullback.fst f f = d ≫ pullback.snd f f := by
    apply hom_ext_of_isIso_restrict f U
    · simp only [Category.assoc, pullback.condition]
    · rintro _ ⟨x, rfl⟩
      change (pullback.snd U.ι h ≫ h) x ∈ U
      rw [← pullback.condition]
      exact (pullback.fst U.ι h x).2
  let ρ := d ≫ pullback.fst f f
  have hρ : ρ ≫ pullback.diagonal f = d := by
    apply pullback.hom_ext
    · simp [ρ]
    · simpa [ρ] using heq
  have hker : (pullback.diagonal f).ker = ⊥ := by
    apply le_bot_iff.mp
    calc
      _ ≤ (ρ ≫ pullback.diagonal f).ker := Scheme.Hom.le_ker_comp _ _
      _ = d.ker := by rw [hρ]
      _ = ⊥ := d.ker_eq_bot
  have : IsIso (pullback.diagonal f) := IsClosedImmersion.isIso_iff_ker_eq_bot.mpr hker
  have : Mono f := (pullback.isIso_diagonal_iff f).mp inferInstance
  exact IsOpenImmersion.of_flat_of_mono f

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
