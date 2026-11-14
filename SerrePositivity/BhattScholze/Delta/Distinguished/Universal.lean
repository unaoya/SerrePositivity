module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.BhattScholze.Delta.Free.FreeDeltaFrobeniusFlat
public import SerrePositivity.BhattScholze.Delta.Extension.DeltaLocalization
import SerrePositivity.CommutativeAlgebra.FlatRegularQuotient
import Mathlib.RingTheory.Flat.Localization

/-!
# distinguished 元をもつ普遍 δ 環

## 概要
BS 著者版 Example 2.21 の ℤ₍ₚ₎{d, δ(d)⁻¹} とその普遍性。

## 方針
一変数自由 δ 環で p と互いに素な自然数と δ(d) を逆にする。分母は Frobenius で閉じる。

## 規約
ここでは完備化の前の環を扱い、元 d の像を指定する。

## 使われ方
BS 著者版 Example 3.4 の普遍向き付き prism の係数環。
-/

@[expose] public noncomputable section

universe u v

namespace SerrePositivity.BhattScholze

/-- 一変数自由 δ 環の初期座標。 -/
abbrev freeDistinguishedGenerator : FreeDeltaRing PUnit.{u+1} :=
  MvPolynomial.X (PUnit.unit, 0)

variable (p : ℕ) [Fact p.Prime]


/-- 概要：普遍 distinguished 環の基本分母。
方針：δ(x) と p に素な自然数で生成する。
規約：BS 著者版 Example 2.21。
使われ方：局所化の普遍性で単元性を確認する。 -/
def distinguishedDenominators : Submonoid (FreeDeltaRing PUnit.{u+1}) :=
  Submonoid.closure (insert ((freeDeltaStructure p PUnit.{u+1}).delta freeDistinguishedGenerator)
    (Set.range (fun n : {n : ℕ // Nat.Coprime n p} => (n.val : (FreeDeltaRing PUnit.{u+1})))))

/-- 概要：distinguished 元をもつ普遍 p 局所 δ 環の台環。
方針：自由 δ 環を基本分母の Frobenius 安定化で局所化する。
規約：BS 著者版 Example 2.21。
使われ方：普遍向き付き prism の未完備モデル。 -/
abbrev UniversalDistinguishedRing :=
  Localization
    ((freeDeltaStructure p PUnit.{u+1}).frobeniusDenominators (distinguishedDenominators p))


/-- 概要：普遍環の δ 構造。
方針：安定な分母による δ 局所化。
規約：BS 著者版 Example 2.21。
使われ方：評価射と完備化の δ 構造。 -/
def universalDistinguishedDelta : DeltaStructure p (UniversalDistinguishedRing.{u} p) :=
  let D := freeDeltaStructure p PUnit.{u+1}
  let M := distinguishedDenominators.{u} p
  D.localization (D.frobeniusDenominators M) (UniversalDistinguishedRing.{u} p)
    (D.frobeniusDenominators_stable M)

/-- 概要：普遍 distinguished 元。
方針：初期座標の局所化像。
規約：BS 著者版 Example 2.21 の d。
使われ方：評価射の指定像および完備化の第二座標。 -/
abbrev universalDistinguishedGenerator : UniversalDistinguishedRing.{u} p :=
  algebraMap (FreeDeltaRing PUnit.{u+1}) (UniversalDistinguishedRing p) freeDistinguishedGenerator

/-- 自由環から普遍環への標準射は δ 射（BS 著者版 Example 2.21）。 -/
theorem universalDistinguished_algebraMap_isDeltaHom :
    (freeDeltaStructure p PUnit.{u+1}).IsDeltaHom (universalDistinguishedDelta p)
      (algebraMap (FreeDeltaRing PUnit.{u+1}) (UniversalDistinguishedRing.{u} p)) :=
  let D := freeDeltaStructure p PUnit.{u+1}
  let M := distinguishedDenominators.{u} p
  D.isDeltaHom_localization (D.frobeniusDenominators M) (UniversalDistinguishedRing.{u} p)
    (D.frobeniusDenominators_stable M)

/-- 概要：普遍元は distinguished。
方針：δ 像は局所化の分母。
規約：BS 著者版 Example 2.21。
使われ方：向き付き prism の構成。 -/
theorem universalDistinguishedGenerator_isDistinguished :
    (universalDistinguishedDelta.{u} p).IsDistinguished (universalDistinguishedGenerator p) := by
  let D := freeDeltaStructure p PUnit.{u+1}
  let M := distinguishedDenominators.{u} p
  have h : D.delta freeDistinguishedGenerator ∈ M :=
    Submonoid.subset_closure (Set.mem_insert _ _)
  unfold DeltaStructure.IsDistinguished
  rw [← universalDistinguished_algebraMap_isDeltaHom p freeDistinguishedGenerator]
  exact IsLocalization.map_units (UniversalDistinguishedRing.{u} p)
    (⟨_, D.le_frobeniusDenominators M h⟩ : D.frobeniusDenominators M)

/-- 概要：指定した distinguished 元への評価は一意な δ 射。
方針：自由環の評価が基本分母を単元に送るため δ 局所化を経由する。
規約：BS 著者版 Example 2.21。標的では p と互いに素な自然数を可逆とする。
使われ方：普遍向き付き prism の評価を完備化の前に構成する。 -/
theorem existsUnique_universalDistinguishedHom {A : Type v} [CommRing A]
    (E : DeltaStructure p A) (b : A) (hb : E.IsDistinguished b)
    (hlocal : ∀ n : ℕ, Nat.Coprime n p → IsUnit (n : A)) :
    ∃! f : UniversalDistinguishedRing.{u} p →+* A,
      (universalDistinguishedDelta p).IsDeltaHom E f ∧
        f (universalDistinguishedGenerator p) = b := by
  let e : (FreeDeltaRing PUnit.{u+1}) →+* A := freeDeltaEval E (fun _ : PUnit.{u+1} ↦ b)
  have he : (freeDeltaStructure p PUnit.{u+1}).IsDeltaHom E e := freeDeltaEval_isDeltaHom E _
  have hx : e freeDistinguishedGenerator = b := by simp [e]
  have hM (s : distinguishedDenominators.{u} p) : IsUnit (e s) := by
    apply Submonoid.closure_induction (motive := fun z _ ↦ IsUnit (e z)) _ _ _ s.property
    · intro z hz
      rcases Set.mem_insert_iff.mp hz with hz | ⟨n, rfl⟩
      · rwa [hz, he, hx]
      · simpa only [map_natCast] using hlocal n.val n.property
    · simp
    · intro a c _ _ ha hc
      rw [map_mul]
      exact ha.mul hc
  obtain ⟨f, hf, hu⟩ :=
    (freeDeltaStructure p PUnit.{u+1}).existsUnique_saturatedLocalization_lift
      (distinguishedDenominators p) (UniversalDistinguishedRing.{u} p) E e he hM
  refine ⟨f, ⟨hf.2, ?_⟩, ?_⟩
  · exact (DFunLike.congr_fun hf.1 freeDistinguishedGenerator).trans hx
  · intro g hg
    apply hu g
    refine ⟨?_, hg.1⟩
    obtain ⟨k, hk, hku⟩ := existsUnique_freeDeltaHom E (fun _ : PUnit.{u+1} ↦ b)
    exact (hku (g.comp (algebraMap (FreeDeltaRing PUnit.{u+1}) (UniversalDistinguishedRing.{u} p)))
      ⟨hg.1.comp (universalDistinguished_algebraMap_isDeltaHom p), fun s ↦ by
        cases s
        exact hg.2⟩).trans (hku e ⟨he, fun s ↦ by cases s; exact hx⟩).symm

/-- 概要：普遍環の (p,d) は弱正則。
方針：自由整数 δ 環での正則性を平坦な局所化へ移す。
規約：BS 著者版 Example 3.4 の完備化前。
使われ方：完備化後の向き付き prism の正則性。 -/
theorem universalDistinguished_regular :
    let L := UniversalDistinguishedRing.{u} p
    let I := Ideal.span {(p : L)}
    IsSMulRegular L (p : L) ∧
      IsSMulRegular (L ⧸ I) (Ideal.Quotient.mk I (universalDistinguishedGenerator p)) := by
  let F := FreeDeltaRing PUnit.{u+1}
  let L := UniversalDistinguishedRing.{u} p
  let D := freeDeltaStructure p PUnit.{u+1}
  let M := D.frobeniusDenominators (distinguishedDenominators p)
  have hp : IsSMulRegular F (p : F) := freeDeltaRing_p_mul_injective p _
  have hmap : algebraMap F L (p : F) = (p : L) := map_natCast _ _
  constructor
  · have h := IsSMulRegular.of_isLocalization L M hp
    rwa [hmap] at h
  · have h := isSMulRegular_mod_of_flat (S := L) (p : F) freeDistinguishedGenerator hp
      (freeDeltaCoordinate_modP_isSMulRegular p PUnit.{u+1} PUnit.unit)
    rwa [hmap] at h

end SerrePositivity.BhattScholze

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Ex 2.21"] _root_.SerrePositivity.BhattScholze.UniversalDistinguishedRing
attribute [cite BS19 "Ex 2.21"] _root_.SerrePositivity.BhattScholze.existsUnique_universalDistinguishedHom
attribute [cite BS19 "Ex 2.21"] _root_.SerrePositivity.BhattScholze.universalDistinguishedGenerator_isDistinguished
attribute [cite BS19 "Ex 2.21"] _root_.SerrePositivity.BhattScholze.universalDistinguished_regular
