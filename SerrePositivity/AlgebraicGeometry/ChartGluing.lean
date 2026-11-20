module

public import SerrePositivity.AlgebraicGeometry.BlowupAway
public import SerrePositivity.AlgebraicGeometry.Exceptional
public import SerrePositivity.AlgebraicGeometry.SeparatedExt

/-!
概要：KST §5 の blowup のアフィンチャートで構成した射を貼り合わせる準備。
方針：標準被覆と、非零因子の局所化からの零核の検出射を用意する。
規約：全て通常のスキームと実際の環準同型で構成する。
使われ方：冪による blowup 比較と一般スキームへの貼り合わせ。
-/

@[expose] public noncomputable section

universe u

namespace SerrePositivity.AlgebraicGeometry

open _root_.AlgebraicGeometry CategoryTheory Limits

variable {R : Type u} [CommRing R] (I : Ideal R)

/--
概要：アフィン blowup の次数一元による実際のアフィン開被覆。
方針：既存の標準チャートの被覆性から各点を含む添字を選ぶ。
規約：KST §5、被覆の各スキームは斉次局所化環の Spec。
使われ方：チャート上の射を `Scheme.Cover.glueMorphisms` に渡す。
-/
def affineBlowupChartCover : (affineBlowup I).AffineOpenCover where
  I₀ := I
  X a := CommRingCat.of (BlowupChartRing I a)
  f a := affineBlowupChartι I a
  idx x := (TopologicalSpace.Opens.mem_iSup.mp
    ((iSup_affineBlowupChart I).ge (Set.mem_univ x))).choose
  covers x := by
    change x ∈ (affineBlowupChartι I _).opensRange
    rw [show (affineBlowupChartι I _).opensRange = affineBlowupChart I _ from
      Proj.opensRange_awayι ..]
    exact (TopologicalSpace.Opens.mem_iSup.mp
      ((iSup_affineBlowupChart I).ge (Set.mem_univ x))).choose_spec

set_option backward.isDefEq.respectTransparency false in
/--
概要：アフィン blowup の構造射は中心の有限生成性なしに分離。
方針：Proj の零次成分上の分離性を、基礎環との同型で移す。
規約：KST §5、固有性に必要な有限生成性は使わない。
使われ方：チャート上の比較射を非被約な重なり上で一意化する。
-/
instance affineBlowupπ_isSeparated : IsSeparated (affineBlowupπ I) := by
  have : IsIso (CommRingCat.ofHom (reesZeroEquiv I).symm.toRingHom) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (reesZeroEquiv I).symm.bijective
  unfold affineBlowupπ
  infer_instance

/--
概要：標準チャート内で a を可逆化した Spec の包含射。
方針：チャート環の通常の局所化準同型に Spec を適用する。
規約：KST §5、a はチャート上の非零因子。
使われ方：チャートの重なり上の比較を検出する射。
-/
def chartLocalizationι (a : I) : Spec (.of (BlowupChartAway I a)) ⟶
    Spec (.of (BlowupChartRing I a)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (BlowupChartRing I a) (BlowupChartAway I a)))

/--
概要：標準チャートの非零因子局所化の Spec の核は零。
方針：非零因子の冪による局所化の単射性を使う。
規約：KST §5、元の環 R で a が零因子でもよい。
使われ方：分離標的への比較射の一意性の検出。
-/
theorem chartLocalizationι_ker_eq_bot (a : I) : (chartLocalizationι I a).ker = ⊥ :=
  specMap_ker_eq_bot_of_injective _
    (IsLocalization.injective (BlowupChartAway I a)
      (Submonoid.powers_le.mpr (chartBaseMap_mem_nonZeroDivisors I a)))

set_option backward.isDefEq.respectTransparency false in
/--
概要：チャートの a 局所化から基底への射の像は D(a) に入る。
方針：係数 a の像が局所化環で単元であることを素イデアルで判定する。
規約：KST §5、実際の構造射との合成について述べる。
使われ方：重なり上の比較射が中心の外で一致することを示す。
-/
theorem chartLocalizationι_range_base (a : I) :
    Set.range (chartLocalizationι I a ≫ affineBlowupChartι I a ≫ affineBlowupπ I) ⊆
      (PrimeSpectrum.basicOpen a.1).carrier := by
  rw [show affineBlowupChartι I a ≫ affineBlowupπ I =
    Spec.map (CommRingCat.ofHom (chartBaseMap I a)) from affineBlowupChartIso_inv_ι_π I a]
  unfold chartLocalizationι
  rw [← Spec.map_comp]
  rintro _ ⟨x, rfl⟩
  change (algebraMap (BlowupChartRing I a) (BlowupChartAway I a)) (chartBaseMap I a a.1)
    ∉ x.asIdeal
  exact Ideal.notMem_of_isUnit _ (IsLocalization.Away.algebraMap_isUnit _)

set_option backward.isDefEq.respectTransparency false in
/--
概要：基底上のチャート射は、標的が分離で中心の外で同型なら重なり上で一致する。
方針：一方のチャートの非零因子局所化を重なりへ引き戻し、零核で一致を検出する。
規約：KST §5、重なりの被約性や元の環での非零因子性は仮定しない。
使われ方：正の冪の blowup 比較射の貼り合わせ。
-/
theorem chart_overlap_hom_ext {Y : Scheme.{u}} (s : Y ⟶ Spec (.of R))
    [IsSeparated s] (a b : I)
    [IsIso (s ∣_ PrimeSpectrum.basicOpen a.1)]
    (f : Spec (.of (BlowupChartRing I a)) ⟶ Y)
    (g : Spec (.of (BlowupChartRing I b)) ⟶ Y)
    (hf : f ≫ s = affineBlowupChartι I a ≫ affineBlowupπ I)
    (hg : g ≫ s = affineBlowupChartι I b ≫ affineBlowupπ I) :
    pullback.fst (affineBlowupChartι I a) (affineBlowupChartι I b) ≫ f =
      pullback.snd (affineBlowupChartι I a) (affineBlowupChartι I b) ≫ g := by
  let j := pullback.fst (affineBlowupChartι I a) (affineBlowupChartι I b)
  let k := pullback.snd (affineBlowupChartι I a) (affineBlowupChartι I b)
  have hbase : (j ≫ f) ≫ s = (k ≫ g) ≫ s := by
    simp only [Category.assoc, hf, hg]
    exact pullback.condition_assoc _
  let ι := pullback.snd (chartLocalizationι I a) j
  apply hom_ext_of_ker_eq_bot_of_separated s hbase ι
    (pullback_snd_ker_eq_bot_of_openImmersion _ (chartLocalizationι_ker_eq_bot I a) j)
  apply hom_ext_of_isIso_restrict s (PrimeSpectrum.basicOpen a.1)
  · simp only [Category.assoc]
    exact congrArg (ι ≫ ·) hbase
  · rw [Category.assoc, Category.assoc, hf]
    rw [← Category.assoc, ← pullback.condition]
    rintro _ ⟨x, rfl⟩
    exact chartLocalizationι_range_base I a ⟨(pullback.fst (chartLocalizationι I a) j) x, rfl⟩

set_option backward.isDefEq.respectTransparency false in
/--
概要：中心の外で同型な分離標的へのアフィン blowup 上の射は、基底上で一意。
方針：標準被覆の各チャートで非零因子局所化を用いて一致を検出する。
規約：KST §5、中心の各元に対応する基本開集合上の同型を仮定する。
使われ方：冪比較の往復が恒等射であることを示す。
-/
theorem affineBlowup_hom_ext {Y : Scheme.{u}} (s : Y ⟶ Spec (.of R))
    [IsSeparated s]
    (hs : ∀ a : I, IsIso (s ∣_ PrimeSpectrum.basicOpen a.1))
    {f g : affineBlowup I ⟶ Y} (h : f ≫ s = affineBlowupπ I)
    (h' : g ≫ s = affineBlowupπ I) : f = g := by
  apply (affineBlowupChartCover I).openCover.hom_ext
  intro a
  change affineBlowupChartι I a ≫ f = affineBlowupChartι I a ≫ g
  have := hs a
  apply hom_ext_of_ker_eq_bot_of_separated s
    (by simp only [Category.assoc, h, h']) (chartLocalizationι I a)
    (chartLocalizationι_ker_eq_bot I a)
  apply hom_ext_of_isIso_restrict s (PrimeSpectrum.basicOpen a.1)
  · simp only [Category.assoc, h, h']
  · simp only [Category.assoc, h]
    rintro _ ⟨x, rfl⟩
    exact chartLocalizationι_range_base I a ⟨x, rfl⟩

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
