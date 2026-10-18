module

public import SerrePositivity.KST.DerivedGeometry.AcyclicMapAttachment
public import SerrePositivity.KST.DerivedGeometry.ExactColimitAcyclic

/-!
概要：acyclic 複体からの対象族の射を単射準同型な拡大で同時に零ホモトピーにする。
方針：完全な coproduct で全ての始域をまとめ、単一射の付加を適用する。
規約：coproduct の完全性を各項自由という条件で代用しない。
使われ方：Stacks Lemma 19.12.4 (079M)、TT §3・§8、Toën §3.2 の非有界分解の一工程。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits
namespace SerrePositivity.KST.DerivedGeometry
variable {C : Type*} [Category* C] [Abelian C] [EnoughInjectives C]
  {σ : Type*} [HasColimitsOfShape (Discrete σ) C] [HasExactColimitsOfShape (Discrete σ) C]
  (A : σ → CochainComplex C ℤ) (M : CochainComplex C ℤ) (w : ∀ i, A i ⟶ M)

/--
概要：完全な coproduct は非輪状な複体の族を非輪状な複体へ送る。
方針：離散図式の余極限に非輪状性保存の一般定理を使う。
規約：全ての次数で完全性を用いる。
使われ方：Stacks Lemma 19.12.4、TT §3 の同時付加の始域。
-/
lemma acyclic_coproduct_of_exactColimits (hA : ∀ i, (A i).Acyclic) : (∐ A).Acyclic :=
  acyclic_colimit_of_exactColimits (.up ℤ) (Discrete.functor A) (fun i => hA i.as)

/--
概要：指定した射の族を同時に殺す拡大先。
方針：全ての射を coproduct からの一つの射へまとめる。
規約：全ての実際の始域の coproduct を使う。
使われ方：Stacks Lemma 19.12.4、Toën §3.2 の同時付加。
-/
def acyclicFamilyAttachment : CochainComplex C ℤ :=
  acyclicMapAttachment (∐ A) M (Sigma.desc w)

/--
概要：同時付加への実際の遷移射。
方針：coproduct の射に対する一射の付加の遷移を使う。
規約：元の M を保持する。
使われ方：Stacks Lemma 19.12.4、TT §3 の超限遷移。
-/
def acyclicFamilyAttachmentι : M ⟶ acyclicFamilyAttachment A M w :=
  acyclicMapAttachmentι (∐ A) M (Sigma.desc w)

/--
概要：同時付加への遷移は単射。
方針：単一射の付加の単射性を使う。
規約：非有界複体。
使われ方：Stacks Lemma 19.12.4、TT §3 の極限での単射性。
-/
instance acyclicFamilyAttachmentι_mono : Mono (acyclicFamilyAttachmentι A M w) :=
  acyclicMapAttachmentι_mono _ _ _

/--
概要：全ての始域が非輪状なら同時付加への遷移は準同型。
方針：完全な coproduct の非輪状性と単一射の付加を使う。
規約：実際の準同型性を証明してから超限工程へ使う。
使われ方：Stacks Lemma 19.12.4、TT §3・§8、Toën §3.2 の同時付加。
-/
lemma acyclicFamilyAttachmentι_quasiIso (hA : ∀ i, (A i).Acyclic) :
    QuasiIso (acyclicFamilyAttachmentι A M w) :=
  acyclicMapAttachmentι_quasiIso _ _ _ (acyclic_coproduct_of_exactColimits A hA)

/--
概要：指定した族の各射は同時付加後に零ホモトピーを持つ。
方針：coproduct からの射の零ホモトピーを各包含に前合成する。
規約：明示的なホモトピーを構成する。
使われ方：Stacks Lemma 19.12.4、TT §3・§8、Toën §3.2 の非有界 K-injective 判定へ向けた工程。
-/
def acyclicFamilyAttachmentNullHomotopy (i : σ) :
    Homotopy (w i ≫ acyclicFamilyAttachmentι A M w) 0 := by
  change Homotopy (w i ≫ acyclicMapAttachmentι (∐ A) M (Sigma.desc w)) 0
  have h := (acyclicMapAttachmentNullHomotopy (∐ A) M (Sigma.desc w)).compLeft (Sigma.ι A i)
  simpa only [← Category.assoc, Sigma.ι_comp_desc, comp_zero] using h

end SerrePositivity.KST.DerivedGeometry
