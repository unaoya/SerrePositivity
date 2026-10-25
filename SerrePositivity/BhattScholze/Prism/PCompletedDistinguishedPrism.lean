module

public import SerrePositivity.BhattScholze.Prism.PCompletedDeltaFunctor
public import SerrePositivity.BhattScholze.Prism.OrientedPrismHom

/-! # d進完備性を明示したp進完備δ完全化のprismと普遍性

著者公開版Lemma 3.9の主イデアル・distinguished生成元の場合の部分定理。
p進完備δ完全化での生成元像のd進完備性を仮定し、実導来条件を持つ完全prismを
具体的に構成する。この完備性自体や一般Cartierイデアルの単項化は結論しない。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (hd : D.IsDistinguished d)
variable [IsAdicComplete (Ideal.span {pCompletedDeltaPerfectionMap D d})
  (PCompletedDeltaPerfection D)]

/-- distinguished生成元の像がd進完備なp進完備δ完全化上の具体的なoriented prism。 -/
def pCompletedDistinguishedPrism : OrientedPrism p (PCompletedDeltaPerfection D) := by
  let := pCompletedDeltaPerfection_isAdicComplete D
  exact OrientedPrism.ofPerfectCompleteDistinguished (pCompletedDeltaPerfectionStructure D)
    (pCompletedDeltaPerfection_isPerfect D) (pCompletedDeltaPerfectionMap D d)
    (pCompletedDeltaPerfectionMap_isDistinguished D hd)

/-- 構成したprismのδ構造は既存のp進完備δ完全化のδ構造。 -/
@[simp] theorem pCompletedDistinguishedPrism_deltaStructure :
    (pCompletedDistinguishedPrism D d hd).deltaStructure =
      pCompletedDeltaPerfectionStructure D := rfl

/-- 構成したprismの選択生成元は元のdの標準像。 -/
@[simp] theorem pCompletedDistinguishedPrism_generator :
    (pCompletedDistinguishedPrism D d hd).generator = pCompletedDeltaPerfectionMap D d := rfl

/-- 構成したprismのイデアルは元の(d)の標準射による像。 -/
theorem pCompletedDistinguishedPrism_ideal :
    (pCompletedDistinguishedPrism D d hd).ideal =
      (Ideal.span {d}).map (pCompletedDeltaPerfectionMap D) := by
  rw [Ideal.map_span, Set.image_singleton]
  rfl

/-- 具体的なprismは完全。 -/
theorem pCompletedDistinguishedPrism_isPerfect :
    (pCompletedDistinguishedPrism D d hd).deltaStructure.IsPerfect :=
  pCompletedDeltaPerfection_isPerfect D

/-- distinguished元を終域のprismイデアルへ送るδ基底射は、
構成したprismから完全oriented prismへの一意な射に延長する。 -/
theorem existsUnique_pCompletedDistinguishedPrismHom
    {B : Type v} [CommRing B] (Q : OrientedPrism p B) (hQ : Q.deltaStructure.IsPerfect)
    (f : A →+* B) (hf : D.IsDeltaHom Q.deltaStructure f) (hdf : f d ∈ Q.ideal) :
    ∃! g : OrientedPrism.Hom (pCompletedDistinguishedPrism D d hd) Q,
      g.toRingHom.comp (pCompletedDeltaPerfectionMap D) = f := by
  let := Q.isAdicComplete_p_of_perfect hQ
  let g := pCompletedDeltaLift D Q.deltaStructure hQ f hf
  have hgj : g.comp (pCompletedDeltaPerfectionMap D) = f := pCompletedDeltaLift_comp_map D _ _ _ _
  have hgd : (pCompletedDeltaPerfectionStructure D).IsDeltaHom Q.deltaStructure g :=
    pCompletedDeltaLift_isDeltaHom D _ _ _ _
  have hgi : (pCompletedDistinguishedPrism D d hd).ideal ≤ Q.ideal.comap g := by
    apply (Ideal.span_singleton_le_iff_mem _).mpr
    change g (pCompletedDeltaPerfectionMap D d) ∈ Q.ideal
    rw [show g (pCompletedDeltaPerfectionMap D d) = f d from RingHom.congr_fun hgj d]
    exact hdf
  let G : OrientedPrism.Hom (pCompletedDistinguishedPrism D d hd) Q := ⟨g, hgd, hgi⟩
  refine ⟨G, hgj, ?_⟩
  intro H hH
  apply OrientedPrism.Hom.ext
  exact pCompletedDeltaLift_unique D Q.deltaStructure hQ f hf H.toRingHom H.map_delta hH

/-- 上の一意性の具体的な公開射。 -/
def pCompletedDistinguishedPrismLift
    {B : Type v} [CommRing B] (Q : OrientedPrism p B) (hQ : Q.deltaStructure.IsPerfect)
    (f : A →+* B) (hf : D.IsDeltaHom Q.deltaStructure f) (hdf : f d ∈ Q.ideal) :
    OrientedPrism.Hom (pCompletedDistinguishedPrism D d hd) Q :=
  (existsUnique_pCompletedDistinguishedPrismHom D d hd Q hQ f hf hdf).choose

/-- prism延長射は標準基底射と可換する。 -/
@[simp] theorem pCompletedDistinguishedPrismLift_comp_map
    {B : Type v} [CommRing B] (Q : OrientedPrism p B) (hQ : Q.deltaStructure.IsPerfect)
    (f : A →+* B) (hf : D.IsDeltaHom Q.deltaStructure f) (hdf : f d ∈ Q.ideal) :
    (pCompletedDistinguishedPrismLift D d hd Q hQ f hf hdf).toRingHom.comp
      (pCompletedDeltaPerfectionMap D) = f :=
  (existsUnique_pCompletedDistinguishedPrismHom D d hd Q hQ f hf hdf).choose_spec.1

/-- 元の生成元の延長像は、終域のprismイデアルを生成する。
単なるイデアル包含ではなく、完全prism間の射の像イデアル一致を使う。 -/
theorem pCompletedDistinguishedPrismLift_map_ideal
    {B : Type v} [CommRing B] (Q : OrientedPrism p B) (hQ : Q.deltaStructure.IsPerfect)
    (f : A →+* B) (hf : D.IsDeltaHom Q.deltaStructure f) (hdf : f d ∈ Q.ideal) :
    (pCompletedDistinguishedPrism D d hd).ideal.map
      (pCompletedDistinguishedPrismLift D d hd Q hQ f hf hdf).toRingHom = Q.ideal :=
  (pCompletedDistinguishedPrismLift D d hd Q hQ f hf hdf).map_ideal_eq_of_perfect
    (pCompletedDistinguishedPrism_isPerfect D d hd) hQ

end SerrePositivity.BhattScholze
