module
public import SerrePositivity.KST.ProExcision.GroupProductData

/-!
# Construction A.6 の外部作用との可換性

概要：u を固定する外部モノイドの作用に関して、共役の実ホモトピーは同変。
方針：各作用準同型に対する区間写像の自然性を特殊化する。
規約：KST Construction A.6、u⁻¹hu の向き。非被約 C(H) の全次数ホモトピー。
使われ方：Lemma 4.16 の補助列を固定する行列の外部作用。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory
variable {G H : Type u} [Monoid G] [Group H]

/-- 概要：u を固定する作用の下で、共役のテンソル区間写像は同変。
方針：A.6 の群準同型に関する自然性を各作用準同型に適用する。
規約：KST Construction A.6、全次数での同変性。
使われ方：Lemma 4.16 の共役比較を G 同変なまま使用する。 -/
lemma conjugationLinearizedHomotopy_equivariant (ρ : G →* Monoid.End H) (u : H)
    (hu : ∀ a, ρ a u = u) :
    LinearizedCylinderEquivariant (discreteNerveAction (MonCat.of G) (MonCat.of H) ρ)
      (discreteNerveAction (MonCat.of G) (MonCat.of H) ρ)
      (conjugationLinearizedHomotopy u).h := by
  intro n a
  have h := conjugationLinearizedHomotopy_naturality (ρ a) u
  rw [hu a] at h
  exact (congrArg (fun q ↦ q.app n) h).symm

/-- 概要：共役の標準区間写像を、同変な区間写像の界面として与える。
方針：A.6 の実区間写像に、u の固定性から得た同変性を付ける。
規約：KST Construction A.6、入力は作用と固定元のみ。
使われ方：作用 bar への持ち上げと Lemma 4.16 の m 次比較。 -/
def conjugationEquivariantCylinderMap (ρ : G →* Monoid.End H) (u : H)
    (hu : ∀ a, ρ a u = u) :
    EquivariantLinearizedCylinderMap (discreteNerveAction (MonCat.of G) (MonCat.of H) ρ)
      (discreteNerveAction (MonCat.of G) (MonCat.of H) ρ) where
  h := (conjugationLinearizedHomotopy u).h
  equivariant := conjugationLinearizedHomotopy_equivariant ρ u hu

end SerrePositivity.KST.ProExcision
