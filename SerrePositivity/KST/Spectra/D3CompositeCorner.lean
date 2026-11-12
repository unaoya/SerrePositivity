module

public import SerrePositivity.KST.Spectra.D3ComparisonHomLifting
public import SerrePositivity.KST.Spectra.RawSpectrumPreWhitehead

/-!
概要：相対左因子の合成に対する元の二変数 Hom corner の全単射 RLP。
方針：第一左因子と第二左因子に同じ右射影の corner 充填を順に適用する。
規約：合成左因子の cofibration 性や corner の RLP を追加入力にしない。
使われ方：d3 の実比較射を相対 BF 分解した後の全 Hom の厳密比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open SerrePositivity.InfinityCategories SerrePositivity.KST.NonConnective
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping

/-- 指定左右境界の可換族に対する元の corner の相対充填を写像として回収する。 -/
lemma d3CornerFamily {A L : OmegaSpectrum.{u}} (a : A ⟶ L)
    (ha : IsSequentialRelativeCofibration a) {E Z : KanSequence.{u}}
    (q : KanSequence.Hom E Z)
    (hq : ∀ n, (MorphismProperty.monomorphisms SSet.{u}).rlp (q.app n).right)
    {V U : SSet.{u}} (j : V ⟶ U) [Mono j] (k : V ⟶ space L E)
    (s : U ⟶ space A E) (t : U ⟶ space L Z)
    (hst : s ≫ post A q = t ≫ pre a Z)
    (hs : k ≫ pre a E = j ≫ s) (ht : k ≫ post L q = j ≫ t) :
    ∃ d : U ⟶ space L E, j ≫ d = k ∧ d ≫ pre a E = s ∧ d ≫ post L q = t := by
  let b := pullback.lift s t hst
  let := relativeCorner_trivialKanFibration a ha q hq
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := relativeCorner a q) j inferInstance
  have hw : k ≫ relativeCorner a q = j ≫ b := by
    apply pullback.hom_ext
    · simpa only [Category.assoc, relativeCorner_fst, b, pullback.lift_fst] using hs
    · simpa only [Category.assoc, relativeCorner_snd, b, pullback.lift_snd] using ht
  let sq : CommSq k j (relativeCorner a q) b := ⟨hw⟩
  refine ⟨sq.lift, sq.fac_left, ?_, ?_⟩
  · have h := congrArg (· ≫ pullback.fst _ _) sq.fac_right
    simpa only [Category.assoc, relativeCorner_fst, b, pullback.lift_fst] using h
  · have h := congrArg (· ≫ pullback.snd _ _) sq.fac_right
    simpa only [Category.assoc, relativeCorner_snd, b, pullback.lift_snd] using h

/-- 二段の相対左因子に沿って、同じ右射影と全境界を保って充填する。 -/
lemma d3CompositeCornerFamily {A L N : OmegaSpectrum.{u}} (a : A ⟶ L) (b : L ⟶ N)
    (ha : IsSequentialRelativeCofibration a) (hb : IsSequentialRelativeCofibration b)
    {E Z : KanSequence.{u}} (q : KanSequence.Hom E Z)
    (hq : ∀ n, (MorphismProperty.monomorphisms SSet.{u}).rlp (q.app n).right)
    {V U : SSet.{u}} (j : V ⟶ U) [Mono j] (k : V ⟶ space N E)
    (s : U ⟶ space A E) (t : U ⟶ space N Z)
    (hst : s ≫ post A q = t ≫ pre (a ≫ b) Z)
    (hs : k ≫ pre (a ≫ b) E = j ≫ s) (ht : k ≫ post N q = j ≫ t) :
    ∃ d : U ⟶ space N E, j ≫ d = k ∧ d ≫ pre (a ≫ b) E = s ∧ d ≫ post N q = t := by
  have hcomm := congrArg Under.Hom.right (pointedPre_post b q)
  simp only [Under.comp_right] at hcomm
  change post N q ≫ pre b Z = pre b E ≫ post L q at hcomm
  obtain ⟨l, hl, hla, hlq⟩ := d3CornerFamily a ha q hq j (k ≫ pre b E) s (t ≫ pre b Z)
    (by simpa only [Category.assoc, ← pre_comp] using hst)
    (by simpa only [Category.assoc, ← pre_comp] using hs)
    (by rw [Category.assoc, ← hcomm, ← Category.assoc, ht, Category.assoc])
  obtain ⟨d, hd, hdb, hdq⟩ := d3CornerFamily b hb q hq j k l t hlq hl.symm ht
  refine ⟨d, hd, ?_, hdq⟩
  rw [pre_comp, ← Category.assoc, hdb, hla]

/-- 合成左因子と元の右射影の二変数 corner の全単射 RLP を実証する。 -/
lemma d3CompositeCorner_trivialKanFibration {A L N : OmegaSpectrum.{u}} (a : A ⟶ L)
    (b : L ⟶ N) (ha : IsSequentialRelativeCofibration a) (hb : IsSequentialRelativeCofibration b)
    {E Z : KanSequence.{u}} (q : KanSequence.Hom E Z)
    (hq : ∀ n, (MorphismProperty.monomorphisms SSet.{u}).rlp (q.app n).right) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (relativeCorner (a ≫ b) q) := by
  constructor
  intro V U j hj
  let : Mono j := hj
  constructor
  intro k z sq
  have hs := congrArg (· ≫ pullback.fst _ _) sq.w
  have ht := congrArg (· ≫ pullback.snd _ _) sq.w
  simp only [Category.assoc, relativeCorner_fst] at hs
  simp only [Category.assoc, relativeCorner_snd] at ht
  have hst : (z ≫ pullback.fst _ _) ≫ post A q =
      (z ≫ pullback.snd _ _) ≫ pre (a ≫ b) Z := by
    rw [Category.assoc, Category.assoc, pullback.condition]
  obtain ⟨d, hd, hda, hdq⟩ := d3CompositeCornerFamily a b ha hb q hq j k
    (z ≫ pullback.fst _ _) (z ≫ pullback.snd _ _) hst hs ht
  refine ⟨⟨{ l := d, fac_left := hd, fac_right := ?_ }⟩⟩
  apply pullback.hom_ext
  · simpa only [Category.assoc, relativeCorner_fst] using hda
  · simpa only [Category.assoc, relativeCorner_snd] using hdq

end SerrePositivity.KST.Spectra.RawSpectrumMapping
