module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.ChartGluing
public import SerrePositivity.AlgebraicGeometry.PowerChartCover

/-!
概要：KST §5 の正の冪によるアフィン blowup の不変性。
方針：対応する純冪チャートの同型を、分離性による一意性で貼り合わせる。
規約：通常の Rees 代数の Proj を用い、冪指数は正とする。
使われ方：KST §5 の厚みの比較と Huneke–Swanson 8.1.5・8.2.1 の有限射。
-/

@[expose] public noncomputable section

universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
variable {R : Type u} [CommRing R] (I : Ideal R)

/--
概要：冪チャートの環同型の逆も基礎環の係数を保存する。
方針：順向きの係数保存に環同型の単射性を適用する。
規約：KST §5、正の冪に限る。
使われ方：チャート比較射が基底上の射であることの証明。
-/
@[simp] theorem powerChartEquiv_symm_base (a : I) (n : ℕ) (hn : 0 < n) (r : R) :
    (powerChartEquiv I a n hn).symm
      (chartBaseMap (I ^ n) (powerCenterElement I a n) r) = chartBaseMap I a r := by
  apply (powerChartEquiv I a n hn).injective
  simp

/--
概要：正の冪の blowup は元の中心の各基本開集合上で同型。
方針：a の n 乗が I の n 乗に入り、D(aⁿ) = D(a) となることを使う。
規約：KST §5、中心の有限生成性は不要。
使われ方：チャート比較を分離性で一意化する。
-/
theorem powerBlowup_restrict_basicOpen_isIso (a : I) (n : ℕ) (hn : 0 < n) :
    IsIso (affineBlowupπ (I ^ n) ∣_ PrimeSpectrum.basicOpen a.1) := by
  have h := affineBlowupπ_restrict_basicOpen_isIso (I ^ n) (powerCenterElement I a n)
  change IsIso (affineBlowupπ (I ^ n) ∣_ PrimeSpectrum.basicOpen (a.1 ^ n)) at h
  rw [PrimeSpectrum.basicOpen_pow a.1 n hn] at h
  exact h

/--
概要：元の中心の純冪に対応するチャートによる冪 blowup のアフィン開被覆。
方針：純冪チャートの被覆性から点ごとの添字を選ぶ。
規約：KST §5、冪指数 n は正。
使われ方：冪 blowup から元の blowup への逆比較射の貼り合わせ。
-/
def affineBlowupPowerChartCover (n : ℕ) (hn : 0 < n) :
    (affineBlowup (I ^ n)).AffineOpenCover where
  I₀ := I
  X a := CommRingCat.of (BlowupChartRing (I ^ n) (powerCenterElement I a n))
  f a := affineBlowupChartι (I ^ n) (powerCenterElement I a n)
  idx x := (TopologicalSpace.Opens.mem_iSup.mp
    ((iSup_affineBlowup_powerCharts I n hn).ge (Set.mem_univ x))).choose
  covers x := by
    change x ∈ (affineBlowupChartι (I ^ n) _).opensRange
    rw [show (affineBlowupChartι (I ^ n) _).opensRange = affineBlowupChart (I ^ n) _ from
      Proj.opensRange_awayι ..]
    exact (TopologicalSpace.Opens.mem_iSup.mp
      ((iSup_affineBlowup_powerCharts I n hn).ge (Set.mem_univ x))).choose_spec

/--
概要：元の blowup の標準チャートから冪 blowup への比較射。
方針：対応するチャート環の同型の逆に Spec を適用する。
規約：KST §5、射は元の blowup から正の冪の blowup へ向かう。
使われ方：冪 blowup の大域比較射の局所成分。
-/
def powerBlowupChartMap (a : I) (n : ℕ) (hn : 0 < n) :
    Spec (.of (BlowupChartRing I a)) ⟶ affineBlowup (I ^ n) :=
  Spec.map (CommRingCat.ofHom (powerChartEquiv I a n hn).symm.toRingHom) ≫
    affineBlowupChartι (I ^ n) (powerCenterElement I a n)

set_option backward.isDefEq.respectTransparency false in
/--
概要：局所的な冪比較射は基礎環上の射。
方針：チャート構造射の計算と環同型の係数保存を使う。
規約：KST §5、比較は実際の構造射との等式。
使われ方：冪比較射の重なり上の一致。
-/
@[reassoc] theorem powerBlowupChartMap_base (a : I) (n : ℕ) (hn : 0 < n) :
    powerBlowupChartMap I a n hn ≫ affineBlowupπ (I ^ n) =
      affineBlowupChartι I a ≫ affineBlowupπ I := by
  unfold powerBlowupChartMap
  have h₀ : affineBlowupChartι I a ≫ affineBlowupπ I =
      Spec.map (CommRingCat.ofHom (chartBaseMap I a)) := affineBlowupChartIso_inv_ι_π I a
  have h₁ : affineBlowupChartι (I ^ n) (powerCenterElement I a n) ≫ affineBlowupπ (I ^ n) =
      Spec.map (CommRingCat.ofHom (chartBaseMap (I ^ n) (powerCenterElement I a n))) :=
    affineBlowupChartIso_inv_ι_π (I ^ n) (powerCenterElement I a n)
  rw [Category.assoc, h₀, h₁, ← Spec.map_comp]
  congr 1
  ext r
  exact congrArg HomogeneousLocalization.val (powerChartEquiv_symm_base I a n hn r)

set_option backward.isDefEq.respectTransparency false in
/--
概要：元のアフィン blowup から正の冪の blowup への大域比較射。
方針：チャート環の比較同型を標準開被覆に沿って貼り合わせる。
規約：KST §5、両立性は標的の分離性と中心外での同型から証明する。
使われ方：冪不変性の同型の順向きの射。
-/
def powerBlowupMap (n : ℕ) (hn : 0 < n) : affineBlowup I ⟶ affineBlowup (I ^ n) :=
  (affineBlowupChartCover I).openCover.glueMorphisms
    (fun a => powerBlowupChartMap I a n hn) (fun a b => by
      have := powerBlowup_restrict_basicOpen_isIso I a n hn
      exact chart_overlap_hom_ext I (affineBlowupπ (I ^ n)) a b _ _
        (powerBlowupChartMap_base I a n hn) (powerBlowupChartMap_base I b n hn))

set_option backward.isDefEq.respectTransparency false in
/--
概要：冪 blowup の大域比較射は基底上の射。
方針：標準開被覆で制限し、局所比較の係数保存に帰着する。
規約：KST §5、構造射との合成の等式として述べる。
使われ方：逆比較射との合成を一意性で恒等射と同定する。
-/
@[reassoc] theorem powerBlowupMap_base (n : ℕ) (hn : 0 < n) :
    powerBlowupMap I n hn ≫ affineBlowupπ (I ^ n) = affineBlowupπ I := by
  apply (affineBlowupChartCover I).openCover.hom_ext
  intro a
  simp only [powerBlowupMap, Scheme.Cover.ι_glueMorphisms_assoc]
  exact powerBlowupChartMap_base I a n hn

/--
概要：冪 blowup の純冪チャートから元の blowup への比較射。
方針：対応するチャート環の同型に Spec を適用する。
規約：KST §5、正の冪に限る。
使われ方：大域比較射の逆射の局所成分。
-/
def powerBlowupChartInv (a : I) (n : ℕ) (hn : 0 < n) :
    Spec (.of (BlowupChartRing (I ^ n) (powerCenterElement I a n))) ⟶ affineBlowup I :=
  Spec.map (CommRingCat.ofHom (powerChartEquiv I a n hn).toRingHom) ≫
    affineBlowupChartι I a

set_option backward.isDefEq.respectTransparency false in
/--
概要：局所的な逆冪比較射も基礎環上の射。
方針：チャート構造射の計算と環同型の係数保存を使う。
規約：KST §5、構造射との等式として述べる。
使われ方：純冪チャート上の逆比較射の貼り合わせ。
-/
@[reassoc] theorem powerBlowupChartInv_base (a : I) (n : ℕ) (hn : 0 < n) :
    powerBlowupChartInv I a n hn ≫ affineBlowupπ I =
      affineBlowupChartι (I ^ n) (powerCenterElement I a n) ≫ affineBlowupπ (I ^ n) := by
  unfold powerBlowupChartInv
  have h₀ : affineBlowupChartι I a ≫ affineBlowupπ I =
      Spec.map (CommRingCat.ofHom (chartBaseMap I a)) := affineBlowupChartIso_inv_ι_π I a
  have h₁ : affineBlowupChartι (I ^ n) (powerCenterElement I a n) ≫ affineBlowupπ (I ^ n) =
      Spec.map (CommRingCat.ofHom (chartBaseMap (I ^ n) (powerCenterElement I a n))) :=
    affineBlowupChartIso_inv_ι_π (I ^ n) (powerCenterElement I a n)
  rw [Category.assoc, h₀, h₁, ← Spec.map_comp]
  congr 1
  ext r
  exact congrArg HomogeneousLocalization.val (powerChartEquiv_base I a n hn r)

/--
概要：元の blowup は中心元の正の冪に対応する基本開集合上で同型。
方針：D(aⁿ) = D(a) により通常の中心外同型に帰着する。
規約：KST §5、a は元の中心 I の元。
使われ方：逆冪比較射を一意化する。
-/
theorem blowup_restrict_power_basicOpen_isIso (a : I) (n : ℕ) (hn : 0 < n) :
    IsIso (affineBlowupπ I ∣_ PrimeSpectrum.basicOpen (powerCenterElement I a n).1) := by
  change IsIso (affineBlowupπ I ∣_ PrimeSpectrum.basicOpen (a.1 ^ n))
  rw [PrimeSpectrum.basicOpen_pow a.1 n hn]
  exact affineBlowupπ_restrict_basicOpen_isIso I a

set_option backward.isDefEq.respectTransparency false in
/--
概要：正の冪のアフィン blowup から元の blowup への大域比較射。
方針：純冪チャート上の比較を被覆に沿って貼り合わせる。
規約：KST §5、純冪チャートが全体を覆うことを利用する。
使われ方：冪不変性の同型の逆向きの射。
-/
def powerBlowupInv (n : ℕ) (hn : 0 < n) : affineBlowup (I ^ n) ⟶ affineBlowup I :=
  (affineBlowupPowerChartCover I n hn).openCover.glueMorphisms
    (fun a => powerBlowupChartInv I a n hn) (fun a b => by
      have := blowup_restrict_power_basicOpen_isIso I a n hn
      exact chart_overlap_hom_ext (I ^ n) (affineBlowupπ I)
        (powerCenterElement I a n) (powerCenterElement I b n) _ _
        (powerBlowupChartInv_base I a n hn) (powerBlowupChartInv_base I b n hn))

set_option backward.isDefEq.respectTransparency false in
/--
概要：大域的な逆冪比較射は基底上の射。
方針：純冪チャート上に制限して係数保存を適用する。
規約：KST §5、構造射との等式。
使われ方：冪比較の往復が恒等射となることの証明。
-/
@[reassoc] theorem powerBlowupInv_base (n : ℕ) (hn : 0 < n) :
    powerBlowupInv I n hn ≫ affineBlowupπ I = affineBlowupπ (I ^ n) := by
  apply (affineBlowupPowerChartCover I n hn).openCover.hom_ext
  intro a
  simp only [powerBlowupInv, Scheme.Cover.ι_glueMorphisms_assoc]
  exact powerBlowupChartInv_base I a n hn

set_option backward.isDefEq.respectTransparency false in
/--
概要：正の冪を中心とするアフィン blowup は元の blowup と同型。
方針：両方向のチャート比較を貼り合わせ、分離性と零核による一意性で逆性を示す。
規約：KST §5、n > 0。任意の可換環と任意のイデアルについて成立する。
使われ方：Lemma 5.6 の古典的部分と Huneke–Swanson 8.1.5・8.2.1 の比較。
-/
def affineBlowupPowerIso (n : ℕ) (hn : 0 < n) :
    affineBlowup (I ^ n) ≅ affineBlowup I where
  hom := powerBlowupInv I n hn
  inv := powerBlowupMap I n hn
  hom_inv_id := affineBlowup_hom_ext (I ^ n) (affineBlowupπ (I ^ n))
    (affineBlowupπ_restrict_basicOpen_isIso (I ^ n))
    (by simp only [Category.assoc, powerBlowupMap_base, powerBlowupInv_base])
    (by simp)
  inv_hom_id := affineBlowup_hom_ext I (affineBlowupπ I)
    (affineBlowupπ_restrict_basicOpen_isIso I)
    (by simp only [Category.assoc, powerBlowupMap_base, powerBlowupInv_base])
    (by simp)

/--
概要：正の冪による blowup の同型は基底上の同型。
方針：逆比較射の基底両立性を適用する。
規約：KST §5、同型は Bl(Iⁿ) から Bl(I) へ向かう。
使われ方：厚みの比較と基底変更の交換式。
-/
@[reassoc] theorem affineBlowupPowerIso_hom_base (n : ℕ) (hn : 0 < n) :
    (affineBlowupPowerIso I n hn).hom ≫ affineBlowupπ I = affineBlowupπ (I ^ n) :=
  powerBlowupInv_base I n hn

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
