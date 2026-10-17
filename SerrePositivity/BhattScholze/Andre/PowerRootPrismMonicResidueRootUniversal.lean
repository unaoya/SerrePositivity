module

public import SerrePositivity.BhattScholze.Andre.PowerRootPolynomialPrismLift
public import SerrePositivity.BhattScholze.Andre.PowerRootPrismMonicRootUniversal

/-!
# André E1・E2：完全試験 prism の剰余根データによる実完備化の普遍性

## 概要

完全試験 prism の商に互換根列を指定し、その第零根が元の多項式の根なら、
raw 実完備化から試験 prism へ基底と剰余根を保つ δ 射が一意に存在する。
BS Rem 7.15（著者版 p.62）の絶対 envelope 比較の完全試験環での段階。

## 方針

共通完備商で入力 δ 射を一意に持ち上げ、元の raw 割り算・実完備化の普遍性を適用する。
原典とは異なる Perfection のモノイド同型・有理指数評価・W₂ 切断による経路。

## 規約

試験 prism の完全性と指定生成元の一致を明示する。
源の prism 商の p 正則性・入力のモニック性は、この普遍射には不要。
一般の試験 prism と絶対 envelope 全体との同定は別工程。

## 使われ方

試験環内の実根列も指定入力 δ 射も引数に残さず、商内の根データから比較射を作る。
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


/-- 概要：完全試験 prism の剰余根データを保つ実完備化からの δ 射は一意に存在。
方針：一意な入力 δ 持上げで分子の可除性を得て、raw 実完備化の普遍性を使う。
規約：根列は商内だけに指定する。試験 prism の完全性と生成元の一致は前提に残す。
使われ方：BS Rem 7.15（著者版 p.62）の完全試験 prism への絶対入力データによる比較。 -/
theorem existsUnique_powerRootPrismMonicCompletionHom_of_perfect_residue_roots
    {B : Type u} [CommRing B] (Q : OrientedPrism p B) (hQ : Q.deltaStructure.IsPerfect)
    (k : A →+* B) (hk : W.deltaStructure.IsDeltaHom Q.deltaStructure k)
    (hd : k W.generator = Q.generator)
    (ρ : ℕ → B ⧸ Q.ideal) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n)
    (hroot : f.eval₂ ((Ideal.Quotient.mk Q.ideal).comp k) (ρ 0) = 0) :
    let := pdCompletionCommRing L p (jL dP)
    ∃! F : H →+* B,
      (DH).IsDeltaHom Q.deltaStructure F ∧
        F.comp (powerRootPrismMonicCompletionBaseMap W hW f) = k ∧
          ∀ n, Ideal.Quotient.mk Q.ideal
            (F (uL (jL (powerRootPolynomialVariable A p hp n)))) = ρ n := by
  let := pdCompletionCommRing L p (jL dP)
  let qB := Ideal.Quotient.mk Q.ideal
  obtain ⟨g, hg, hgu⟩ :=
    existsUnique_powerRootPolynomialDeltaHom_of_perfectPrism_residue_roots p hW.p_mul_injective
      W.deltaStructure Q hQ k hk ρ hρ
  have hdg : g dP = Q.generator := (RingHom.congr_fun hg.2.1 W.generator).trans hd
  have hinput : g (powerRootMonicPDInput p f) =
      f.eval₂ k (g (powerRootPolynomialVariable A p hp 0)) := by
    unfold powerRootMonicPDInput powerRootPolynomialBaseMap
    rw [Polynomial.aeval_def, Polynomial.hom_eval₂, hg.2.1]
  have hzero : qB (g (powerRootMonicPDInput p f)) = 0 := by
    calc
      _ = qB (f.eval₂ k (g (powerRootPolynomialVariable A p hp 0))) := congrArg qB hinput
      _ = f.eval₂ (qB.comp k) (qB (g (powerRootPolynomialVariable A p hp 0))) :=
        Polynomial.hom_eval₂ f k qB _
      _ = 0 := by
        rw [show qB (g (powerRootPolynomialVariable A p hp 0)) = ρ 0 from hg.2.2 0]
        exact hroot
  have hr : Function.Injective (fun x : B => g dP * x) := by
    rw [hdg]
    exact Q.generator_regular
  have ha : ∀ s, g dP ∣ g (a s) := by
    intro s
    rw [hdg]
    exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hzero)
  have hc : IsModuleComplete B (g dP) (ModuleCat.of B B) := by
    rw [hdg]
    exact Q.complete_generator
  obtain ⟨F, hF, hu⟩ := existsUnique_rawDeltaDivisionPDHom E Q.deltaStructure dP a g hg.1 hr ha
    Q.complete_p hc
  refine ⟨F, ⟨hF.1, ?_, ?_⟩, ?_⟩
  · change (F.comp ((uL).comp jL)).comp (algebraMap A P) = k
    rw [hF.2]
    exact hg.2.1
  · intro n
    exact (congrArg qB (RingHom.congr_fun hF.2 (powerRootPolynomialVariable A p hp n))).trans
      (hg.2.2 n)
  · intro K hK
    let gK := K.comp ((uL).comp jL)
    have hKδ : (E).IsDeltaHom Q.deltaStructure gK :=
      hK.1.comp ((pdCompletionUnit_isDeltaHom DL (jL dP)).comp
        (deltaAdjoinDivisionMap_isDeltaHom E dP a))
    have hgK : gK = g := hgu gK ⟨hKδ, hK.2.1, hK.2.2⟩
    exact hu K ⟨hK.1, hgK⟩

end SerrePositivity.BhattScholze.Andre
