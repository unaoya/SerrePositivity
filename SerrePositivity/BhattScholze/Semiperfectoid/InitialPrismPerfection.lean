module
public meta import SerrePositivity.Util.Citation

public import SerrePositivity.BhattScholze.Prism.Perfection.ClassicalPrismPerfection
public import SerrePositivity.BhattScholze.Prism.Perfectoid.PerfectoidPrismPresentation
public import SerrePositivity.BhattScholze.Prism.Perfectoid.PerfectPrismHomLift

/-!
# 初期 prism の完全化と perfectoid 化

## 概要
全有界標的への初期剰余単位を完全化し、完全 prism への始性と perfectoid 化を得る。
## 方針
非完全な源の完全化の普遍性と、完全 prism・perfectoid 環の既存の対応を使う。
## 規約
BS 著者版 Proposition 7.10。Δ との同一視を含まない。
## 使われ方
S′ の初期包絡の完全化と Corollary 7.3 の比較。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Semiperfectoid
open CategoryTheory Prismatic
set_option backward.isDefEq.respectTransparency false
variable {p : ℕ} [Fact p.Prime] {T B : Type u} [CommRing T] [CommRing B]

/-- 剰余単位を指定した、全有界試験 prism への始性。 -/
def IsInitialPrismUnit (Q : OrientedPrism p B) (v : T →+* B ⧸ Q.ideal) : Prop :=
  ∀ (C : Type u) [CommRing C] (Y : OrientedPrism p C) (hY : IsBoundedPrism Y)
    (s : T →+* C ⧸ Y.ideal), ∃! g : OrientedPrism.Hom Q Y, g.quotientMap.comp v = s

/-- 剰余単位を指定した、完全な試験 prism への始性。 -/
def IsPerfectInitialPrismUnit (Q : OrientedPrism p B) (v : T →+* B ⧸ Q.ideal) : Prop :=
  ∀ (C : Type u) [CommRing C] (Y : OrientedPrism p C) (hY : Y.deltaStructure.IsPerfect)
    (s : T →+* C ⧸ Y.ideal), ∃! g : OrientedPrism.Hom Q Y, g.quotientMap.comp v = s

/-- 初期剰余単位と完全化の標準射の合成。 -/
def classicalPrismPerfectionUnit (Q : OrientedPrism p B) (v : T →+* B ⧸ Q.ideal) :
    T →+* classicalPrismPerfectionCoefficients Q ⧸ (classicalPrismPerfection Q).ideal :=
  (classicalPrismPerfectionMap Q).quotientMap.comp v

/-- 概要：全有界標的への始性は、完全化後の完全標的への始性を与える。
方針：元の初期射を完全化から一意に延長し、二つの一意性を使う。
規約：BS 著者版 Proposition 7.10。源を完全とは仮定しない。
使われ方：S′ 単位を保つ完全 prism の比較。 -/
theorem classicalPrismPerfection_initial (Q : OrientedPrism p B) (v : T →+* B ⧸ Q.ideal)
    (hv : IsInitialPrismUnit Q v) :
    IsPerfectInitialPrismUnit (classicalPrismPerfection Q) (classicalPrismPerfectionUnit Q v) := by
  intro C _ Y hY s
  have hbY : IsBoundedPrism Y := ⟨1, fun n x hx => by
    simpa only [pow_one] using Y.quotient_p_pow_torsion_killed_by_p hY n x hx⟩
  obtain ⟨f, hf, hfu⟩ := hv C Y hbY s
  obtain ⟨g, hg, hgu⟩ := existsUnique_classicalPrismPerfectionHom Q Y hY f
  refine ⟨g, ?_, ?_⟩
  · change g.quotientMap.comp ((classicalPrismPerfectionMap Q).quotientMap.comp v) = s
    rw [← RingHom.comp_assoc, ← OrientedPrism.Hom.quotientMap_comp, hg, hf]
  · intro k hk
    apply hgu
    apply hfu
    rw [OrientedPrism.Hom.quotientMap_comp, RingHom.comp_assoc]
    exact hk

/-- 概要：完全 prism の剰余単位の完全標的への始性は、環としての perfectoid 化を与える。
方針：任意の perfectoid 標的を有界な完全 prism の商で表示し、Lemma 4.8 で射を持ち上げる。
規約：BS 著者版 Theorem 3.10・Proposition 7.10。零環を含む。
使われ方：Corollary 7.3 の候補との単位を保つ比較。 -/
theorem isPerfectoidization_of_perfectInitial (Q : OrientedPrism p B)
    (hQ : Q.deltaStructure.IsPerfect) (v : T →+* B ⧸ Q.ideal)
    (hv : IsPerfectInitialPrismUnit Q v) : IsPerfectoidization p v := by
  refine ⟨Q.quotient_isIntegralPerfectoid hQ, ?_⟩
  intro C _ hC s
  obtain ⟨A, P, hP, hPb, ⟨e⟩⟩ := exists_boundedPerfectPrismPresentation p C hC
  obtain ⟨g, hg, hgu⟩ := hv A P hP (e.symm.toRingHom.comp s)
  refine ⟨e.toRingHom.comp g.quotientMap, ?_, ?_⟩
  · change (e.toRingHom.comp g.quotientMap).comp v = s
    rw [RingHom.comp_assoc, hg]
    apply RingHom.ext
    intro x
    exact e.apply_symm_apply (s x)
  · intro l hl
    obtain ⟨k, hk, _⟩ := _root_.SerrePositivity.BhattScholze.existsUnique_perfectPrismHomLift_to_bounded Q hQ P hPb
      (e.symm.toRingHom.comp l)
    have hkg : k = g := by
      apply hgu
      rw [hk, RingHom.comp_assoc, hl]
    apply RingHom.ext
    intro x
    calc
      l x = e (e.symm (l x)) := (e.apply_symm_apply (l x)).symm
      _ = e (k.quotientMap x) := congrArg e (RingHom.congr_fun hk x).symm
      _ = e (g.quotientMap x) := by rw [hkg]

/-- 初期 prism の完全化の商は、元の環の普遍 perfectoid 化。 -/
theorem classicalPrismPerfectionUnit_isPerfectoidization (Q : OrientedPrism p B)
    (v : T →+* B ⧸ Q.ideal) (hv : IsInitialPrismUnit Q v) :
    IsPerfectoidization p (classicalPrismPerfectionUnit Q v) :=
  isPerfectoidization_of_perfectInitial _ (classicalPrismPerfection_isPerfect Q) _
    (classicalPrismPerfection_initial Q v hv)

end SerrePositivity.BhattScholze.Semiperfectoid

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Prop 7.10" (partial := component) "BS-W17 H5（11-12）：T（有限）と S′（任意添字）の古典的な部分は本体：固定 A_inf 上の有界な実包絡、全有界 prism への一意な射、S′ の完全化と Cor 7.3 の単位を保つ唯一の同型（停止点 4・5a・5）。S′ の単位の完全忠実平坦性は後回し（E3 は使わない）。Δ_R/A との同定（G10）は drafts ／ 11-12 節の見直し：S′ の部分は f_j=0 の場合（根の商）だけ"] _root_.SerrePositivity.BhattScholze.Semiperfectoid.classicalPrismPerfection_initial
