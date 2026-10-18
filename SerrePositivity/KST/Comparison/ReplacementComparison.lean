module

public import SerrePositivity.KST.Comparison.HomotopyPullback
public import SerrePositivity.KST.Comparison.FiberwisePullback

/-!
# 基底上の Kan 分解の比較

概要：同じ右射の二つの anodyne–Kan 分解の引き戻しを比較する。
方針：分解間の持ち上げと基底を固定する実ホモトピーで互いに逆な射を作る。
規約：Segal 1974 Proposition 1.6・Lemma 1.7 の引き戻し模型の比較。
使われ方：bar の積射影を都合のよい Kan 分解で計算する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits
open SerrePositivity.SimplicialModel

/--
概要：同じ基底上の射の間の写像を、任意の基底変換で引き戻す。
方針：第一射影を保ち、第二射影を基底上の写像へ送る。
規約：Segal 1974 Lemma 1.7 の比較の規約。
使われ方：二つの Kan 分解の引き戻し比較。
-/
def pullbackMapBase {T₀ T₁ X B : SSet.{u}} (p₀ : T₀ ⟶ B) (p₁ : T₁ ⟶ B)
    (f : X ⟶ B) (k : T₀ ⟶ T₁) (hk : k ≫ p₁ = p₀) : pullback f p₀ ⟶ pullback f p₁ :=
  pullback.lift (pullback.fst f p₀) (pullback.snd f p₀ ≫ k) (by
    rw [Category.assoc, hk]
    exact pullback.condition)

/--
概要：基底上の引き戻し比較の第一射影は元の第一射影である。
方針：引き戻しの計算則を使う。
規約：Segal 1974 Lemma 1.7。
使われ方：二分解の比較の合成則。
-/
@[reassoc] theorem pullbackMapBase_fst {T₀ T₁ X B : SSet.{u}}
    (p₀ : T₀ ⟶ B) (p₁ : T₁ ⟶ B) (f : X ⟶ B) (k : T₀ ⟶ T₁) (hk : k ≫ p₁ = p₀) :
    pullbackMapBase p₀ p₁ f k hk ≫ pullback.fst f p₁ = pullback.fst f p₀ := pullback.lift_fst ..

/--
概要：基底上の引き戻し比較の第二射影は元の写像との合成である。
方針：引き戻しの計算則を使う。
規約：Segal 1974 Lemma 1.7。
使われ方：二分解の比較の合成の同定。
-/
@[reassoc] theorem pullbackMapBase_snd {T₀ T₁ X B : SSet.{u}}
    (p₀ : T₀ ⟶ B) (p₁ : T₁ ⟶ B) (f : X ⟶ B) (k : T₀ ⟶ T₁) (hk : k ≫ p₁ = p₀) :
    pullbackMapBase p₀ p₁ f k hk ≫ pullback.snd f p₁ = pullback.snd f p₀ ≫ k := pullback.lift_snd ..

/--
概要：互いに逆向きの基底上の写像の引き戻しの合成は合成写像の引き戻しである。
方針：二つの射影で比較する。
規約：Segal 1974 Lemma 1.7 の関手性。
使われ方：基底上のホモトピー逆を引き戻す。
-/
theorem pullbackMapBase_comp {T₀ T₁ X B : SSet.{u}}
    (p₀ : T₀ ⟶ B) (p₁ : T₁ ⟶ B) (f : X ⟶ B)
    (k : T₀ ⟶ T₁) (hk : k ≫ p₁ = p₀) (l : T₁ ⟶ T₀) (hl : l ≫ p₀ = p₁) :
    pullbackMapBase p₀ p₁ f k hk ≫ pullbackMapBase p₁ p₀ f l hl =
      pullbackMapOver p₀ f (k ≫ l) (by rw [Category.assoc, hl, hk]) := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullbackMapBase_fst, pullbackMapBase_fst, pullbackMapOver_fst]
  · rw [Category.assoc, pullbackMapBase_snd, pullbackMapOver_snd,
      ← Category.assoc (pullbackMapBase p₀ p₁ f k hk), pullbackMapBase_snd, Category.assoc]
/--
概要：同じ射の二つの anodyne–Kan 分解の基底上の比較は、任意の引き戻しで局所化同型となる。
方針：逆向きの持ち上げを作り、二つの合成を包含と基底を固定する実ホモトピーで恒等へ結ぶ。
規約：Segal 1974 Proposition 1.6・Lemma 1.7。基底の Kan 性は不要。
使われ方：ホモトピー引き戻し模型を別の Kan 分解で計算する。
-/
theorem replacementComparison_pullback_isIso {A T₀ T₁ X B : SSet.{u}}
    (i₀ : A ⟶ T₀) (hi₀ : SSet.anodyneExtensions i₀)
    (i₁ : A ⟶ T₁) (hi₁ : SSet.anodyneExtensions i₁)
    (p₀ : T₀ ⟶ B) (hp₀ : SSet.modelCategoryQuillen.J.rlp p₀)
    (p₁ : T₁ ⟶ B) (hp₁ : SSet.modelCategoryQuillen.J.rlp p₁)
    (ha : i₀ ≫ p₀ = i₁ ≫ p₁) (k : T₀ ⟶ T₁) (hik : i₀ ≫ k = i₁) (hkp : k ≫ p₁ = p₀)
    (f : X ⟶ B) : IsIso (AnodyneHomotopy.anodyneQ.map (pullbackMapBase p₀ p₁ f k hkp)) := by
  have : HasLiftingProperty i₁ p₀ := hi₁ _ hp₀
  let sq : CommSq i₀ i₁ p₀ p₁ := ⟨ha⟩
  let l := sq.lift
  have hil : i₁ ≫ l = i₀ := sq.fac_left
  have hlp : l ≫ p₀ = p₁ := sq.fac_right
  have hkl : (k ≫ l) ≫ p₀ = p₀ := by rw [Category.assoc, hlp, hkp]
  have hlk : (l ≫ k) ≫ p₁ = p₁ := by rw [Category.assoc, hkp, hlp]
  obtain ⟨H₀, _, hb₀⟩ := anodyne_fiberwise_homotopy i₀ hi₀ p₀ hp₀ (𝟙 T₀) (k ≫ l) i₀
    (Category.comp_id i₀) (by rw [← Category.assoc, hik, hil]) p₀ (Category.id_comp p₀) hkl
  obtain ⟨H₁, _, hb₁⟩ := anodyne_fiberwise_homotopy i₁ hi₁ p₁ hp₁ (𝟙 T₁) (l ≫ k) i₁
    (Category.comp_id i₁) (by rw [← Category.assoc, hil, hik]) p₁ (Category.id_comp p₁) hlk
  let K := pullbackMapBase p₀ p₁ f k hkp
  let L := pullbackMapBase p₁ p₀ f l hlp
  have hK : K ≫ L = pullbackMapOver p₀ f (k ≫ l) hkl := pullbackMapBase_comp p₀ p₁ f k hkp l hlp
  have hL : L ≫ K = pullbackMapOver p₁ f (l ≫ k) hlk := pullbackMapBase_comp p₁ p₀ f l hlp k hkp
  have e₀ := AnodyneHomotopy.map_homotopy_eq AnodyneHomotopy.anodyneQ
    (Localization.inverts AnodyneHomotopy.anodyneQ SSet.anodyneExtensions)
    (pullbackHomotopyOver p₀ f (Category.id_comp p₀) hkl H₀ hb₀)
  have e₁ := AnodyneHomotopy.map_homotopy_eq AnodyneHomotopy.anodyneQ
    (Localization.inverts AnodyneHomotopy.anodyneQ SSet.anodyneExtensions)
    (pullbackHomotopyOver p₁ f (Category.id_comp p₁) hlk H₁ hb₁)
  rw [pullbackMapOver_id, ← hK, AnodyneHomotopy.anodyneQ.map_id,
    AnodyneHomotopy.anodyneQ.map_comp] at e₀
  rw [pullbackMapOver_id, ← hL, AnodyneHomotopy.anodyneQ.map_id,
    AnodyneHomotopy.anodyneQ.map_comp] at e₁
  let e : AnodyneHomotopy.anodyneQ.obj (pullback f p₀) ≅
      AnodyneHomotopy.anodyneQ.obj (pullback f p₁) :=
    { hom := AnodyneHomotopy.anodyneQ.map K
      inv := AnodyneHomotopy.anodyneQ.map L
      hom_inv_id := e₀.symm
      inv_hom_id := e₁.symm }
  exact e.isIso_hom


end SerrePositivity.KST.Comparison
