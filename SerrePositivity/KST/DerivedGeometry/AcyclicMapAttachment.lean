module

public import SerrePositivity.KST.DerivedGeometry.InjectiveFactorExpansion
public import SerrePositivity.KST.DerivedGeometry.ShortExactPushout

/-!
概要：指定された acyclic 複体からの射を単射準同型な拡大で零ホモトピーにする。
方針：指定した acyclic 複体の contractible な埋め込みを、その射に沿って押し出す。
規約：任意の非有界複体。小さい対象族の全射の同時付加は別工程。
使われ方：Stacks Lemma 19.12.4 (079M)、TT §3・§8、Toën §3.2 の非有界分解の構成部品。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits
namespace SerrePositivity.KST.DerivedGeometry
variable {C : Type*} [Category* C] [Abelian C] [EnoughInjectives C]
  (A M : CochainComplex C ℤ) (w : A ⟶ M)

/--
概要：acyclic な複体間の任意の鎖写像は準同型。
方針：全てのコホモロジーが零であることから同型性を判定する。
規約：非有界複体。
使われ方：Stacks Lemma 19.12.4、TT §3 の付加の余核の消滅。
-/
lemma quasiIso_of_acyclic (f : A ⟶ M) (hA : A.Acyclic) (hM : M.Acyclic) : QuasiIso f := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  exact (hA n).isZero_homology.isIso (hM n).isZero_homology _

/--
概要：指定した射に沿って contractible な埋め込みを押し出した短複体。
方針：既証の injective 埋め込みの短完全列を左端で押し出す。
規約：第一項は元の M。
使われ方：Stacks Lemma 19.12.4、Toën §3.2 の指定した射の付加。
-/
def acyclicMapAttachmentShortComplex : ShortComplex (CochainComplex C ℤ) :=
  shortComplexPushout (injectiveEnvelopeShortComplex A) w

/--
概要：押し出した短複体は短完全。
方針：短完全列の押し出しの一般補題を使う。
規約：A の非輪状性はこの段階では不要。
使われ方：Stacks Lemma 19.12.4、TT §3 の単射準同型性の判定。
-/
lemma acyclicMapAttachmentShortComplex_shortExact : (acyclicMapAttachmentShortComplex A M w).ShortExact :=
  shortComplexPushout_shortExact _ _ (injectiveEnvelopeShortComplex_shortExact A)

/--
概要：指定された射を殺すための実際の拡大先。
方針：押し出した短完全列の中央対象を取る。
規約：K-injectivity はまだ主張しない。
使われ方：Stacks Lemma 19.12.4、TT §3・§8 の付加の一工程。
-/
def acyclicMapAttachment : CochainComplex C ℤ := (acyclicMapAttachmentShortComplex A M w).X₂

/--
概要：元の複体から指定した射を殺す拡大への鎖写像。
方針：押し出した短完全列の第一射を取る。
規約：元の対象 M を保持する。
使われ方：Stacks Lemma 19.12.4、Toën §3.2 の超限反復の遷移射。
-/
def acyclicMapAttachmentι : M ⟶ acyclicMapAttachment A M w :=
  (acyclicMapAttachmentShortComplex A M w).f

/--
概要：付加への遷移は単射。
方針：実際の短完全性を適用する。
規約：非輪状性は単射性に不要。
使われ方：Stacks Lemma 19.12.4、TT §3 の極限での単射性。
-/
instance acyclicMapAttachmentι_mono : Mono (acyclicMapAttachmentι A M w) :=
  (acyclicMapAttachmentShortComplex_shortExact A M w).mono_f

/--
概要：始域 A が非輪状なら付加への遷移は準同型。
方針：contractible な埋め込みへの射の余核が非輪状であり、押し出し後の余核も同じものを使う。
規約：分解の存在・準同型性をフィールドで仮定しない。
使われ方：Stacks Lemma 19.12.4、TT §3・§8、Toën §3.2 の acyclic 射を殺す工程。
-/
lemma acyclicMapAttachmentι_quasiIso (hA : A.Acyclic) : QuasiIso (acyclicMapAttachmentι A M w) := by
  have hJ : (termInjectiveEnvelope A).Acyclic := adjacentBiproductComplex_acyclic _
  have hi : QuasiIso (termInjectiveEnvelopeι A) := quasiIso_of_acyclic A _ _ hA hJ
  have hQ := (injectiveEnvelopeShortComplex_shortExact A).acyclic_X₃ hi
  exact shortExact_quasiIso_f_of_acyclic (acyclicMapAttachmentShortComplex A M w)
    (acyclicMapAttachmentShortComplex_shortExact A M w) hQ

/--
概要：指定した射は付加への遷移の後で零ホモトピーを持つ。
方針：contractible な複体の縮約を押し出しのもう一つの射へ合成する。
規約：非輪状性はこの零ホモトピー自体に不要。
使われ方：Stacks Lemma 19.12.4、TT §3・§8、Toën §3.2 の K-injective 判定へ向けた工程。
-/
def acyclicMapAttachmentNullHomotopy : Homotopy (w ≫ acyclicMapAttachmentι A M w) 0 := by
  have h : Homotopy (termInjectiveEnvelopeι A) 0 := by
    simpa using (adjacentBiproductContraction (fun n => Injective.under (A.X n))).compLeft
      (termInjectiveEnvelopeι A)
  let b : termInjectiveEnvelope A ⟶ acyclicMapAttachment A M w :=
    shortComplexPushoutOther (injectiveEnvelopeShortComplex A) w
  have ht : Homotopy (termInjectiveEnvelopeι A ≫ b) 0 := by
    simpa only [zero_comp] using h.compRight b
  have hw : w ≫ acyclicMapAttachmentι A M w = termInjectiveEnvelopeι A ≫ b :=
    shortComplexPushout_comm (injectiveEnvelopeShortComplex A) w
  exact (Homotopy.ofEq hw).trans ht

end SerrePositivity.KST.DerivedGeometry
