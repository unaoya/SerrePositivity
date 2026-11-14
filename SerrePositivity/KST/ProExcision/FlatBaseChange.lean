module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.KST.ProExcision.KoszulPro
public import Mathlib.RingTheory.Flat.CategoryTheory

@[expose] public noncomputable section

set_option maxSynthPendingDepth 10
set_option backward.isDefEq.respectTransparency false

/-!
# 平坦係数への底変換

概要：ホモロジー・イデアル倍・pro-零性の平坦底変換をまとめる。
方針：平坦テンソル関手のホモロジー保存と既存のイデアル倍比較を使う。
規約：H は R 加群として平坦ならよく、H の環の可換性は要求しない。
使われ方：KST Lemma 4.9・4.10 の非可換平坦係数版。
-/

universe u

namespace SerrePositivity.KST.ProExcision

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open HomologicalComplex
open scoped TensorProduct

variable {R : Type u} [CommRing R]

/-- 概要：平坦テンソル積は複体のホモロジーと自然に可換。
方針：平坦な右テンソル関手が有限極限・有限余極限を保つことを使う。
規約：π_n と複体ホモロジーの同定は K-L9 が供給する。
使われ方：KST Lemma 4.10 の π_*(B ⊗ H) = π_*(B) ⊗ H の複体側の比較。 -/
def flatTensorHomologyIso (H : ModuleCat.{u} R) [Module.Flat R H] (q : ℤ) :
    (tensorRight H).mapHomologicalComplex (.up ℤ) ⋙ homologyFunctor _ _ q ≅
      homologyFunctor _ _ q ⋙ tensorRight H := by
  let : PreservesFiniteColimits (tensorRight H) :=
    preservesFiniteColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight H)
  let : (tensorRight H).PreservesHomology := Functor.preservesHomologyOfExact _
  exact NatIso.ofComponents (fun K ↦ (K.sc q).mapHomologyIso (tensorRight H))
    (fun f ↦ ShortComplex.mapHomologyIso_hom_naturality
      ((shortComplexFunctor _ _ q).map f) (tensorRight H))

/-- 概要：イデアル倍のテンソル像はテンソル後のイデアル倍。
方針：既存の生成元による計算を使う。規約：この等式には平坦性不要。
使われ方：KST §4 の a(n)M の底変換。 -/
theorem ideal_smul_tensor_range (I : Ideal R) (M H : ModuleCat.{u} R) :
    LinearMap.range ((I • (⊤ : Submodule R M)).subtype.rTensor H) =
      I • (⊤ : Submodule R (M ⊗[R] H)) :=
  range_rTensor_smul_top I

/-- 概要：テンソル関手は加群の塔の pro-零性を保つ。
方針：テンソルが零射を保つことを用いる。規約：平坦性不要。
使われ方：KST Lemma 4.9 の消滅を係数 H に移す。 -/
theorem tensor_proZero {X : Tower (ModuleCat.{u} R)} (hX : IsProZero X)
    (H : ModuleCat.{u} R) : IsProZero (X.map (tensorRight H)) :=
  hX.map (tensorRight H) (fun {_ _} ↦ Functor.map_zero _ _ _)

/-- 概要：テンソル関手は加群の塔の pro 同型を保つ。
方針：一般の関手の保存補題を適用する。規約：平坦性不要。
使われ方：正本 §2.6 L3、有理化を含む係数変更。 -/
theorem tensor_proIso {X Y : Tower (ModuleCat.{u} R)} {f : LevelHom X Y}
    (hf : IsProIso f) (H : ModuleCat.{u} R) : IsProIso (f.map (tensorRight H)) :=
  hf.map (tensorRight H)

/-- 概要：平坦テンソルはホモロジー上で零になる複体射を保つ。
方針：ホモロジー底変換同型の自然性で零射を移す。
規約：複体射自体の零性は要求しない。使われ方：KST Lemma 4.9 の平坦係数版。 -/
theorem flatTensor_homologyMap_zero (H : ModuleCat.{u} R) [Module.Flat R H]
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ L) (q : ℤ)
    (hf : homologyMap f q = 0) :
    homologyMap (((tensorRight H).mapHomologicalComplex (.up ℤ)).map f) q = 0 := by
  let iso := flatTensorHomologyIso H q
  have hn := iso.hom.naturality f
  dsimp only [Functor.comp_map] at hn
  change homologyMap (((tensorRight H).mapHomologicalComplex (.up ℤ)).map f) q ≫
    iso.hom.app L = iso.hom.app K ≫ (tensorRight H).map (homologyMap f q) at hn
  rw [hf, Functor.map_zero, comp_zero] at hn
  exact (cancel_mono (iso.hom.app L)).mp (by simpa using hn)

/-- 概要：平坦底変換は複体の塔のホモロジー pro-零性を保つ。
方針：零になるホモロジー遷移へ自然な底変換同型を適用する。
規約：次数ごとに別の消滅指数を許す。使われ方：KST Lemma 4.9・4.10 の係数版。 -/
theorem flatTensor_homology_proZero (H : ModuleCat.{u} R) [Module.Flat R H]
    (X : Tower (CochainComplex (ModuleCat.{u} R) ℤ)) (q : ℤ)
    (hX : IsProZero (X.map (homologyFunctor _ _ q))) :
    IsProZero ((X.map ((tensorRight H).mapHomologicalComplex (.up ℤ))).map
      (homologyFunctor _ _ q)) := by
  intro n
  obtain ⟨m, h, hz⟩ := hX n
  exact ⟨m, h, flatTensor_homologyMap_zero H (X.transition h) q hz⟩

/-- 概要：有限生成加群の Koszul ホモロジーの pro-消滅は平坦係数変更後も成り立つ。
方針：Lemma 4.9 の有限生成加群版とホモロジー底変換を合成する。
規約：M ⊗ H 自体の有限生成性は仮定しない。使われ方：KST Lemma 4.9 の非可換平坦係数版。 -/
theorem koszul_flatTensor_homology_proZero [IsNoetherianRing R]
    {e : ℕ} (z : Fin e → R) (M H : ModuleCat.{u} R)
    [Module.Finite R M] [Module.Flat R H] (q : ℤ) (hq : q < 0) :
    IsProZero (((koszulTensorTower z M).map
      ((tensorRight H).mapHomologicalComplex (.up ℤ))).map (homologyFunctor _ _ q)) :=
  flatTensor_homology_proZero H (koszulTensorTower z M) q
    (koszulTensorHomologyTower_isProZero z M q hq)

end SerrePositivity.KST.ProExcision

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite KST "Lemma 4.1" (partial := component) "仮定：Noether 環上の有限加群の Koszul 塔と平坦底変換（Lean が強い）。結論：Koszul の正次数ホモロジーのプロ消滅を平坦底変換へ移す。一般のプロ単体環の導来テンソルは含まない（Lean が弱い）。"] _root_.SerrePositivity.KST.ProExcision.koszul_flatTensor_homology_proZero
attribute [cite LT "Lemma 2.29" (partial := component) "仮定：同一の可換基礎環上の通常加群の自然数塔と固定加群（Lean が強い）。結論：通常テンソルでプロ同型を保つ。基礎環と両加群が動く導来テンソルでの π プロ同値は含まない（Lean が弱い）。"] _root_.SerrePositivity.KST.ProExcision.tensor_proIso
