module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
概要：KST §5 の幾何学的比較に使う、分離標的へのスキーム射の一意性。
方針：等化子の閉埋め込みの核を、核が零の比較射を通して消す。
規約：被約性や点集合の稠密性で代用せず、イデアル層の核を使う。
使われ方：blowup のチャート比較の貼り合わせと Claim 5.3 の古典的な幾何入力。
-/

@[expose] public noncomputable section

universe u

namespace SerrePositivity.AlgebraicGeometry

open _root_.AlgebraicGeometry CategoryTheory Limits

set_option backward.isDefEq.respectTransparency false in
/--
概要：単射な環準同型の Spec のスキーム論的核は零。
方針：Spec の大域切断と元の環の自然同型を使って、切断の写像の単射性を示す。
規約：KST §5、環は任意の可換環、射の全射性は仮定しない。
使われ方：非零因子による局所化の Spec が比較射の一意性を検出することを示す。
-/
theorem specMap_ker_eq_bot_of_injective {A B : CommRingCat.{u}} (φ : A ⟶ B)
    (hφ : Function.Injective φ) : (Spec.map φ).ker = ⊥ := by
  have hcomp : Function.Injective
      (((Spec.map φ).appTop ≫ (Scheme.ΓSpecIso B).hom).hom) := by
    rw [Scheme.ΓSpecIso_naturality]
    exact hφ.comp (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso A).hom).1
  have happ : Function.Injective (Spec.map φ).appTop := by
    intro x y hxy
    apply hcomp
    change (Scheme.ΓSpecIso B).hom ((Spec.map φ).appTop x) =
      (Scheme.ΓSpecIso B).hom ((Spec.map φ).appTop y)
    rw [hxy]
  apply Scheme.IdealSheafData.ext_of_isAffine
  simpa [(Spec.map φ).ker_apply ⟨⊤, isAffineOpen_top (Spec A)⟩,
    ← RingHom.injective_iff_ker_eq_bot] using happ

set_option backward.isDefEq.respectTransparency false in
/--
概要：核が零の射の後で一致する二つの基底上の射は、標的が分離なら一致する。
方針：基底上の等化子は閉埋め込みで、その核は比較射の零核に含まれる。
規約：KST §5、原像側の被約性は仮定しない。
使われ方：blowup の標準チャート上で構成した射の重なり上の一意性。
-/
theorem hom_ext_of_ker_eq_bot_of_separated {W X Y S : Scheme.{u}}
    (s : Y ⟶ S) [IsSeparated s] {f g : X ⟶ Y} (h : f ≫ s = g ≫ s)
    (ι : W ⟶ X) (hι : ι.ker = ⊥) (hU : ι ≫ f = ι ≫ g) : f = g := by
  let X' : Over S := Over.mk (f ≫ s)
  let Y' : Over S := Over.mk s
  let W' : Over S := Over.mk (ι ≫ f ≫ s)
  let f' : X' ⟶ Y' := Over.homMk f
  let g' : X' ⟶ Y' := Over.homMk g
  let ι' : W' ⟶ X' := Over.homMk ι
  have : IsSeparated Y'.hom := ‹IsSeparated s›
  let l : W' ⟶ equalizer f' g' := equalizer.lift ι' (by ext1; exact hU)
  have hl : l.left ≫ (equalizer.ι f' g').left = ι := by
    change (l ≫ equalizer.ι f' g').left = _
    rw [equalizer.lift_ι]
    rfl
  have hker : (equalizer.ι f' g').left.ker = ⊥ := by
    apply le_bot_iff.mp
    calc
      _ ≤ (l.left ≫ (equalizer.ι f' g').left).ker := Scheme.Hom.le_ker_comp _ _
      _ = ι.ker := by rw [hl]
      _ = ⊥ := hι
  have : IsIso (equalizer.ι f' g').left :=
    IsClosedImmersion.isIso_iff_ker_eq_bot.mpr hker
  rw [← cancel_epi (equalizer.ι f' g').left]
  congrm $(equalizer.condition f' g').left

set_option backward.isDefEq.respectTransparency false in
/--
概要：核が零の準コンパクト射は、開埋め込みによる基底変換後も核が零。
方針：開基底変換での核イデアルの切断公式をアフィン開集合ごとに適用する。
規約：KST §5、被約性を仮定せずスキーム論的な核を使う。
使われ方：チャートの重なりに非零因子局所化の検出射を引き戻す。
-/
theorem pullback_snd_ker_eq_bot_of_openImmersion {X Y V : Scheme.{u}}
    (f : X ⟶ Y) [QuasiCompact f] (hf : f.ker = ⊥)
    (j : V ⟶ Y) [IsOpenImmersion j] : (pullback.snd f j).ker = ⊥ := by
  apply Scheme.IdealSheafData.ext
  funext W
  rw [Scheme.ker_ideal_of_isPullback_of_isOpenImmersion f (pullback.snd f j)
    (pullback.fst f j) j (IsPullback.of_hasPullback f j).flip W, hf]
  ext x
  exact map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso (j.appIso W).inv).1

set_option backward.isDefEq.respectTransparency false in
/--
概要：標的の構造射が U 上で同型なら、U の上に入る基底上の二つの射は一致する。
方針：二つの射を U の逆像へ持ち上げ、制限した構造射の単射性で比較する。
規約：KST §5、射の像が基底の U に入ることを明示する。
使われ方：中心の補集合上でチャート比較の二つの射が一致することを示す。
-/
theorem hom_ext_of_isIso_restrict {X Y S : Scheme.{u}} (s : Y ⟶ S) (U : S.Opens)
    [IsIso (s ∣_ U)] {f g : X ⟶ Y} (h : f ≫ s = g ≫ s)
    (hU : Set.range (f ≫ s) ⊆ U) : f = g := by
  have hf : Set.range f ⊆ s ⁻¹ᵁ U := by
    rintro _ ⟨x, rfl⟩
    exact hU ⟨x, rfl⟩
  have hg : Set.range g ⊆ s ⁻¹ᵁ U := by
    rintro _ ⟨x, rfl⟩
    change (g ≫ s) x ∈ U
    rw [← h]
    exact hU ⟨x, rfl⟩
  let fU := IsOpenImmersion.lift (s ⁻¹ᵁ U).ι f (by simpa using hf)
  let gU := IsOpenImmersion.lift (s ⁻¹ᵁ U).ι g (by simpa using hg)
  have hfg : fU = gU := by
    apply (cancel_mono (s ∣_ U)).mp
    apply (cancel_mono U.ι).mp
    dsimp only [fU, gU]
    simp only [Category.assoc, morphismRestrict_ι, IsOpenImmersion.lift_fac_assoc]
    exact h
  calc
    f = fU ≫ (s ⁻¹ᵁ U).ι := (IsOpenImmersion.lift_fac _ _ _).symm
    _ = gU ≫ (s ⁻¹ᵁ U).ι := by rw [hfg]
    _ = g := IsOpenImmersion.lift_fac _ _ _

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
