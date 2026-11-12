module

public import SerrePositivity.KST.Spectra.D3CompositeCorner

/-!
概要：BF 対象を両端に持つ Hom corner を、元の豊穣 Hom の表記へ移す。
方針：一般 BF 変数の段階で Raw Hom の前後合成を照合し、同じ全単射 RLP を回収する。
規約：具体的な逐次 BF 置換の全定義を Hom の法則ごとに展開しない。
使われ方：d3 共通解像の豊穣構造を元の Hom のまま検証する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open SerrePositivity.InfinityCategories SerrePositivity.KST.NonConnective
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
local instance spectrumCornerCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

/-- 元の BF 豊穣合成の通常表記を一般対象の段階で固定する。 -/
lemma common_eComp (X Y Z : OmegaSpectrum.{u}) :
    eComp SSet X Y Z = mappingComposition X Y Z := rfl

/-- 元の BF 豊穣恒等の通常表記を一般対象の段階で固定する。 -/
lemma common_eId (X : OmegaSpectrum.{u}) : eId SSet X = mappingIdentity X := rfl

/-- 元の Raw 後合成の、同じ BF 豊穣 whiskering による表示。 -/
lemma commonPost_spectrum (X : OmegaSpectrum.{u}) {Y Z : OmegaSpectrum.{u}} (f : Y ⟶ Z) :
    RawSpectrumMapping.post X
      (⟨f.app, f.comm⟩ : KanSequence.Hom Y.toKanSequence Z.toKanSequence) =
      eHomWhiskerLeft SSet X f :=
  RawSpectrumMapping.post_spectrum X f

/-- BF 豊穣 Hom の指定した左右境界を記憶する空間。 -/
abbrev spectrumCornerTarget {A L E Z : OmegaSpectrum.{u}} (a : A ⟶ L) (q : E ⟶ Z) :=
  pullback (eHomWhiskerLeft SSet A q) (eHomWhiskerRight SSet a Z)

/-- 同じ実 BF Hom を、指定した左右境界へ写す corner。 -/
def spectrumCorner {A L E Z : OmegaSpectrum.{u}} (a : A ⟶ L) (q : E ⟶ Z) :
    mappingSpace L E ⟶ spectrumCornerTarget a q :=
  pullback.lift (eHomWhiskerRight SSet a E) (eHomWhiskerLeft SSet L q)
    (by exact (eHom_whisker_exchange SSet a q).symm)

@[reassoc (attr := simp)]
lemma spectrumCorner_fst {A L E Z : OmegaSpectrum.{u}} (a : A ⟶ L) (q : E ⟶ Z) :
    spectrumCorner a q ≫ pullback.fst _ _ = eHomWhiskerRight SSet a E :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma spectrumCorner_snd {A L E Z : OmegaSpectrum.{u}} (a : A ⟶ L) (q : E ⟶ Z) :
    spectrumCorner a q ≫ pullback.snd _ _ = eHomWhiskerLeft SSet L q :=
  pullback.lift_snd _ _ _

/-- BF 変数の段階で、同じ corner の基底変換の左境界を証明する。 -/
@[reassoc]
lemma spectrumCorner_pullback_fst {A L E Z : OmegaSpectrum.{u}} (a : A ⟶ L) (q : E ⟶ Z)
    {U : SSet.{u}} (f : U ⟶ spectrumCornerTarget a q) :
    pullback.fst (spectrumCorner a q) f ≫ eHomWhiskerRight SSet a E =
      pullback.snd (spectrumCorner a q) f ≫ f ≫ pullback.fst _ _ := by
  have h := congrArg (· ≫ pullback.fst _ _) (pullback.condition (f := spectrumCorner a q) (g := f))
  simpa only [Category.assoc, spectrumCorner_fst] using h

/-- BF 変数の段階で、同じ corner の基底変換の右境界を証明する。 -/
@[reassoc]
lemma spectrumCorner_pullback_snd {A L E Z : OmegaSpectrum.{u}} (a : A ⟶ L) (q : E ⟶ Z)
    {U : SSet.{u}} (f : U ⟶ spectrumCornerTarget a q) :
    pullback.fst (spectrumCorner a q) f ≫ eHomWhiskerLeft SSet L q =
      pullback.snd (spectrumCorner a q) f ≫ f ≫ pullback.snd _ _ := by
  have h := congrArg (· ≫ pullback.snd _ _) (pullback.condition (f := spectrumCorner a q) (g := f))
  simpa only [Category.assoc, spectrumCorner_snd] using h

/-- 同じ二段左因子の実 Raw corner の全単射 RLP を BF 豊穣表記に回収する。 -/
lemma spectrumCompositeCorner_trivialKanFibration {A L N E Z : OmegaSpectrum.{u}}
    (a : A ⟶ L) (b : L ⟶ N) (ha : IsSequentialRelativeCofibration a)
    (hb : IsSequentialRelativeCofibration b) (q : E ⟶ Z)
    (hq : ∀ n, (MorphismProperty.monomorphisms SSet.{u}).rlp (q.app n).right) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (spectrumCorner (a ≫ b) q) := by
  constructor
  intro V U j hj
  let : Mono j := hj
  constructor
  intro k z sq
  have hs := congrArg (· ≫ pullback.fst _ _) sq.w
  have ht := congrArg (· ≫ pullback.snd _ _) sq.w
  simp only [Category.assoc, spectrumCorner_fst] at hs
  simp only [Category.assoc, spectrumCorner_snd] at ht
  let qr : KanSequence.Hom E.toKanSequence Z.toKanSequence := ⟨q.app, q.comm⟩
  have hst : (z ≫ pullback.fst _ _) ≫ RawSpectrumMapping.post A qr =
      (z ≫ pullback.snd _ _) ≫ RawSpectrumMapping.pre (a ≫ b) Z.toKanSequence := by
    dsimp only [qr]
    rw [commonPost_spectrum, RawSpectrumMapping.pre_spectrum,
      Category.assoc, Category.assoc, pullback.condition]
  have hs' : k ≫ RawSpectrumMapping.pre (a ≫ b) E.toKanSequence =
      j ≫ (z ≫ pullback.fst _ _) := by
    rw [RawSpectrumMapping.pre_spectrum]
    exact hs
  have ht' : k ≫ RawSpectrumMapping.post N qr = j ≫ (z ≫ pullback.snd _ _) := by
    dsimp only [qr]
    rw [commonPost_spectrum]
    exact ht
  obtain ⟨d, hd, hda, hdq⟩ := RawSpectrumMapping.d3CompositeCornerFamily a b ha hb qr hq
    j k (z ≫ pullback.fst _ _) (z ≫ pullback.snd _ _) hst hs' ht'
  refine ⟨⟨{ l := d, fac_left := hd, fac_right := ?_ }⟩⟩
  apply pullback.hom_ext
  · rw [Category.assoc, spectrumCorner_fst]
    rw [RawSpectrumMapping.pre_spectrum] at hda
    exact hda
  · rw [Category.assoc, spectrumCorner_snd]
    dsimp only [qr] at hdq
    rw [commonPost_spectrum] at hdq
    exact hdq

/-- 同じ BF 比較正方形への Raw 右射影の後合成を一般対象の段階で検査する。 -/
lemma spectrumWhiskeredProjection {A B C D : OmegaSpectrum.{u}}
    (c : A ⟶ B) (d : C ⟶ D) {Z : KanSequence.{u}}
    (q : KanSequence.Hom D.toKanSequence Z) {U : SSet.{u}}
    (f : U ⟶ mappingSpace A C) (g : U ⟶ mappingSpace B D)
    (h : f ≫ eHomWhiskerLeft SSet A d = g ≫ eHomWhiskerRight SSet c D) :
    f ≫ RawSpectrumMapping.post A
      ((⟨d.app, d.comm⟩ : KanSequence.Hom C.toKanSequence D.toKanSequence).comp q) =
      g ≫ RawSpectrumMapping.post B q ≫ RawSpectrumMapping.pre c Z := by
  have he := congrArg Under.Hom.right (RawSpectrumMapping.pointedPre_post c q)
  simp only [Under.comp_right] at he
  change RawSpectrumMapping.post B q ≫ RawSpectrumMapping.pre c Z =
    RawSpectrumMapping.pre c D.toKanSequence ≫ RawSpectrumMapping.post A q at he
  rw [RawSpectrumMapping.post_comp, ← Category.assoc, commonPost_spectrum, h,
    Category.assoc, ← RawSpectrumMapping.pre_spectrum, ← he]

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
