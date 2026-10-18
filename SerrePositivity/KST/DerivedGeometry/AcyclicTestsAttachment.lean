module

public import SerrePositivity.KST.DerivedGeometry.AcyclicFamilyAttachment

/-!
概要：固定した試験複体の族から現在の複体への全ての射を同時に殺す。
方針：試験対象と実際の鎖写像の組を添字にする coproduct の付加を構成する。
規約：その添字の coproduct の存在と完全性を用いる。
使われ方：Stacks Lemma 19.12.4 (079M)、TT §3・§8、Toën §3.2 の非有界 K-injective 分解の一工程。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits
namespace SerrePositivity.KST.DerivedGeometry
variable {C : Type*} [Category* C] [Abelian C] [EnoughInjectives C]
  {σ : Type*} (A : σ → CochainComplex C ℤ) (M : CochainComplex C ℤ)

/--
概要：試験複体とその始域を持つ現在の全ての鎖写像の添字。
方針：依存和で実際の射を列挙する。
規約：新しい射の存在は仮定しない。
使われ方：Stacks Lemma 19.12.4、TT §3 の同時付加。
-/
abbrev acyclicTestMapIndex := Σ i, A i ⟶ M

variable [HasColimitsOfShape (Discrete (acyclicTestMapIndex A M)) C]
  [HasExactColimitsOfShape (Discrete (acyclicTestMapIndex A M)) C]

/--
概要：試験対象族からの全ての現在の射を殺す拡大先。
方針：各射を添字に持つ族を同時付加する。
規約：K-injective 性は超限工程の後で判定する。
使われ方：Stacks Lemma 19.12.4、Toën §3.2 の非有界分解。
-/
def acyclicTestsAttachment : CochainComplex C ℤ :=
  acyclicFamilyAttachment (fun t : acyclicTestMapIndex A M => A t.1) M (fun t => t.2)

/--
概要：試験対象の全射を殺す拡大への遷移。
方針：構成済みの同時付加の遷移を使う。
規約：元の M を保持する。
使われ方：Stacks Lemma 19.12.4、TT §3 の超限遷移。
-/
def acyclicTestsAttachmentι : M ⟶ acyclicTestsAttachment A M :=
  acyclicFamilyAttachmentι (fun t : acyclicTestMapIndex A M => A t.1) M (fun t => t.2)

/-- 概要：試験対象の全射の付加は単射。
方針：族の同時付加の単射性を使う。
規約：非有界。使われ方：Stacks Lemma 19.12.4、TT §3 の単射な超限遷移。 -/
instance acyclicTestsAttachmentι_mono : Mono (acyclicTestsAttachmentι A M) :=
  acyclicFamilyAttachmentι_mono _ _ _

/--
概要：全ての試験複体が非輪状なら全射の付加は準同型。
方針：完全な coproduct と証明済みの同時付加を使う。
規約：準同型性を未証明のフィールドとして要求しない。
使われ方：Stacks Lemma 19.12.4、TT §3・§8 の超限工程。
-/
lemma acyclicTestsAttachmentι_quasiIso (hA : ∀ i, (A i).Acyclic) :
    QuasiIso (acyclicTestsAttachmentι A M) :=
  acyclicFamilyAttachmentι_quasiIso _ _ _ (fun t => hA t.1)

/--
概要：各試験複体から現在の対象への任意の射は遷移後に零ホモトピーを持つ。
方針：その射自身を添字とする同時付加の零ホモトピーを取る。
規約：全射を明示的に列挙した実際の構成。
使われ方：Stacks Lemma 19.12.4、TT §3・§8、Toën §3.2 の K-injective 判定へ向けた工程。
-/
def acyclicTestsAttachmentNullHomotopy (i : σ) (f : A i ⟶ M) :
    Homotopy (f ≫ acyclicTestsAttachmentι A M) 0 :=
  acyclicFamilyAttachmentNullHomotopy (fun t : acyclicTestMapIndex A M => A t.1) M
    (fun t => t.2) ⟨i, f⟩

end SerrePositivity.KST.DerivedGeometry
