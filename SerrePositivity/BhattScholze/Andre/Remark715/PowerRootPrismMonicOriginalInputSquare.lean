module

public import SerrePositivity.BhattScholze.Andre.Remark715.PowerRootPrismMonicStandardCompletedInput
public import SerrePositivity.BhattScholze.Andre.Remark715.PowerRootPrismMonicEquationInputSquare
public import SerrePositivity.BhattScholze.Andre.Remark715.PowerRootMonicCompletedInputExt
public import SerrePositivity.BhattScholze.Andre.Remark715.PowerRootPrismMonicOriginalCompletedInput

/-!
# André A1-a：原典の完備入力作用を保つ実完備化の普遍性

## 概要

H/d の通常の p 完備性の明示仮定の下で、原典の完備入力環の標準作用を保つ
H から有界試験 prism への δ 射は一意に存在する。BS Rem 7.15（著者版 p.62）の比較。

## 方針

完備な標的への入力射の外延性を使い、全根の保存から入力環全体の可換性を得る。
原典を補う、主商・完備化の外延性と明示的な可換図式による経路。

## 規約

H/d の p 完備性 hT はこのファイルで解消せず、H 自体の prism 性も結論しない。
条件付きの入力作用を含む普遍性を絶対 envelope の同定完了とは数えない。

## 使われ方

並列成果から完備性・生成元正則性が到着したときの絶対 envelope 比較の合流点。
-/

@[expose] public noncomputable section
universe u
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open SerrePositivity.DerivedCompletion
variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
variable (f : Polynomial A)
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "P" => PowerRootPolynomial A p hp
local notation "E" => powerRootPolynomialDelta p hW.p_mul_injective W.deltaStructure
local notation "dP" => algebraMap A P W.generator
local notation "a" => powerRootPrismMonicUnaryFamily (p := p) f
local notation "L" => DeltaAdjoinDivision E dP a
local notation "jL" => deltaAdjoinDivisionMap E dP a
local notation "H" => PDCompletionH0 L p (jL dP)
local notation "uL" => pdCompletionUnit L p (jL dP)
local notation "T" => H ⧸ Ideal.span {uL (jL dP)}
local notation "R" => A ⧸ W.ideal
local notation "v" => perfectPrismVarpi W hW
local notation "φ" => powerRootPrismMonicHodgeTateBaseMap W hW f



local notation "DL" => deltaAdjoinDivisionStructure E dP a
local notation "DH" => deltaPDCompletionStructure DL (jL dP)


local notation "fR" => f.map (Ideal.Quotient.mk W.ideal)
local notation "PR" => PowerRootPolynomial R p hp
local notation "CR" => AdicCompletion (Ideal.span {(p : PR)}) PR
local notation "zR" => powerRootPolynomialBaseMap R p hp fR
local notation "SI" => PowerRootMonicCompletedInput p hp fR
local notation "lS" => RingHom.comp
  (Ideal.Quotient.mk (Ideal.span {algebraMap PR CR zR})) (algebraMap PR CR)
local notation "S₀" => PowerRootEquationQuotient p hp fR
local notation "CS" => AdicCompletion (Ideal.span {(p : S₀)}) S₀
local notation "jS" => algebraMap S₀ CS
local notation "qR" => Ideal.Quotient.mk (Ideal.span {zR})

variable {B : Type u} [CommRing B] (Q : OrientedPrism p B)
variable (k : OrientedPrism.Hom W Q)
local notation "qB" => Ideal.Quotient.mk Q.ideal
local notation "baseH" => powerRootPrismMonicCompletionBaseMap W hW f
local notation "φ₀" => powerRootPrismMonicHodgeTateBaseMap W hW f
variable (hf : f.Monic)

set_option maxHeartbeats 800000 in
-- 元の H⁰ と完備入力の依存する環構造・係数作用を同時に照合するため。
/-- 概要：完備入力図式の可換性は全ての標準根の保存と同値。
方針：標的の p 完備性を有界試験 prism から供給し、係数と全根の外延性を使う。
規約：H/d の p 完備性を明示仮定にする。
使われ方：BS Rem 7.15（著者版 p.62）の完備入力作用を含む普遍性。 -/
theorem powerRootPrismMonicOriginalInputSquare_iff_roots
    (hB : ∃ N : ℕ, ∀ n : ℕ, ∀ x : B ⧸ Q.ideal,
      (p : B ⧸ Q.ideal) ^ n * x = 0 → (p : B ⧸ Q.ideal) ^ N * x = 0)
    (η : SI →+* B ⧸ Q.ideal)
    (hη : (η.comp lS).comp (algebraMap R PR) = k.quotientMap) :
    let := pdCompletionCommRing L p (jL dP)
    ∀ (hT : IsAdicComplete (Ideal.span {(p : T)}) T)
      (F : H →+* B) (hF : F.comp baseH = k.toRingHom),
      (powerRootPrismMonicReductionMap W hW f Q k F hF).comp
        (powerRootPrismMonicOriginalInputMap W hW f hf hT) = η ↔
          ∀ n, qB (F (uL (jL (powerRootPolynomialVariable A p hp n)))) =
            η (lS (powerRootPolynomialVariable R p hp n)) := by
  let := pdCompletionCommRing L p (jL dP)
  dsimp only
  intro hT F hF
  let : IsAdicComplete (Ideal.span {(p : B ⧸ Q.ideal)}) (B ⧸ Q.ideal) :=
    boundedPrism_quotient_isAdicComplete_prime Q hB
  constructor
  · intro hs n
    have h := RingHom.congr_fun hs (lS (powerRootPolynomialVariable R p hp n))
    rw [RingHom.comp_apply, powerRootPrismMonicOriginalInputMap_root] at h
    exact h
  · intro hr
    apply powerRootMonicCompletedInput_ringHom_ext p hp fR
    · apply RingHom.ext
      intro x
      change powerRootPrismMonicReductionMap W hW f Q k F hF
        (powerRootPrismMonicOriginalInputMap W hW f hf hT (lS (algebraMap R PR x))) =
          η (lS (algebraMap R PR x))
      have hc := RingHom.congr_fun (powerRootPrismMonicOriginalInputMap_coeff W hW f hf hT) x
      change powerRootPrismMonicOriginalInputMap W hW f hf hT
        (lS (algebraMap R PR x)) = φ₀ x at hc
      rw [hc]
      exact (RingHom.congr_fun (powerRootPrismMonicReductionMap_coeff W hW f Q k F hF) x).trans
        (RingHom.congr_fun hη x).symm
    · intro n
      change powerRootPrismMonicReductionMap W hW f Q k F hF
        (powerRootPrismMonicOriginalInputMap W hW f hf hT
          (lS (powerRootPolynomialVariable R p hp n))) =
            η (lS (powerRootPolynomialVariable R p hp n))
      rw [powerRootPrismMonicOriginalInputMap_root]
      exact hr n

set_option maxHeartbeats 800000 in
-- 元の H⁰ と完備入力図式の依存型を保ったまま一意存在を移すため。
/-- 概要：原典の完備入力作用を保つ H から有界試験 prism への δ 射は一意に存在。
方針：根保存の普遍性を、完備入力図式の可換性との同値で言い換える。
規約：hT と H 自体の prism 性の解消は別工程に残す。
使われ方：BS Rem 7.15（著者版 p.62）の絶対 envelope 比較の入力作用を含む接続点。 -/
theorem existsUnique_powerRootPrismMonicHom_preserving_original_input
    (hB : ∃ N : ℕ, ∀ n : ℕ, ∀ x : B ⧸ Q.ideal,
      (p : B ⧸ Q.ideal) ^ n * x = 0 → (p : B ⧸ Q.ideal) ^ N * x = 0)
    (η : SI →+* B ⧸ Q.ideal)
    (hη : (η.comp lS).comp (algebraMap R PR) = k.quotientMap) :
    let := pdCompletionCommRing L p (jL dP)
    ∀ hT : IsAdicComplete (Ideal.span {(p : T)}) T,
    ∃! F : H →+* B, (DH).IsDeltaHom Q.deltaStructure F ∧
      ∃ hF : F.comp baseH = k.toRingHom,
        (powerRootPrismMonicReductionMap W hW f Q k F hF).comp
          (powerRootPrismMonicOriginalInputMap W hW f hf hT) = η := by
  let := pdCompletionCommRing L p (jL dP)
  dsimp only
  intro hT
  obtain ⟨F, hF, hu⟩ := existsUnique_powerRootPrismMonicCompletionHom_of_original_completed_input
    W hW f hf Q hB k η hη
  refine ⟨F, ⟨hF.1, ⟨hF.2.1, ?_⟩⟩, ?_⟩
  · exact (powerRootPrismMonicOriginalInputSquare_iff_roots W hW f Q k hf hB η hη hT F hF.2.1).mpr
      (hF.2.2)
  · rintro K ⟨hKδ, hK, hs⟩
    exact hu K ⟨hKδ, hK,
      (powerRootPrismMonicOriginalInputSquare_iff_roots W hW f Q k hf hB η hη hT K hK).mp hs⟩

end SerrePositivity.BhattScholze.Andre
