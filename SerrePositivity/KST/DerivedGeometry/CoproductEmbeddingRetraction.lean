module

public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms

/-!
概要：添字集合の埋め込みによる定数対象の直和の切断・縮約を構成する。
方針：像に含まれる添字では元の添字の包含を使い、像の外では零射を使う。
規約：空の添字も許す。
使われ方：Stacks 19.12.1・19.12.2、TT §3・§8、Toën §3.2 の直和の添字の上界。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits
open scoped Classical
namespace SerrePositivity.KST.DerivedGeometry
variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  {σ τ : Type*} (G : C) (e : σ ↪ τ)
  [HasCoproduct (fun _ : σ => G)] [HasCoproduct (fun _ : τ => G)]

/--
概要：添字集合の埋め込みによる定数直和の射。
方針：各項を埋め込み先の対応する項へ含める。
規約：有限性を仮定しない。
使われ方：Stacks 19.12.1、TT §3 の直和の添字の上界。
-/
def coproductEmbeddingSection : (∐ fun _ : σ => G) ⟶ (∐ fun _ : τ => G) :=
  Sigma.desc (fun s => Sigma.ι (fun _ : τ => G) (e s))

/--
概要：埋め込まれた添字の定数直和への縮約。
方針：像の外は零射とし、像の中では単射性で一意な元の添字を用いる。
規約：空の添字にも適用する。
使われ方：Stacks 19.12.1、TT §3 の小さい直和から大きい直和への比較。
-/
def coproductEmbeddingRetraction : (∐ fun _ : τ => G) ⟶ (∐ fun _ : σ => G) :=
  Sigma.desc (fun t => if h : ∃ s, e s = t then Sigma.ι (fun _ : σ => G) h.choose else 0)

/--
概要：定数直和の添字の埋め込みと縮約の合成は恒等。
方針：各直和成分で添字の単射性を使って検証する。
規約：明示的な右逆を与える。
使われ方：Stacks 19.12.1、TT §3 の小さい全射部分対象の統一した上界。
-/
lemma coproductEmbeddingSection_comp_retraction :
    coproductEmbeddingSection G e ≫ coproductEmbeddingRetraction G e = 𝟙 _ := by
  apply Sigma.hom_ext
  intro s
  simp only [coproductEmbeddingSection, coproductEmbeddingRetraction,
    Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc, Category.comp_id]
  rw [dite_eq_left (show ∃ x, e x = e s from ⟨s, rfl⟩)]
  congr 1
  exact e.injective (Exists.choose_spec (show ∃ x, e x = e s from ⟨s, rfl⟩))

/--
概要：添字の埋め込みに対応する縮約は全射。
方針：構成済みの右逆を使う。
規約：任意の零射を持つ圏。
使われ方：Stacks 19.12.1・19.12.2、TT §3 の直和の上界。
-/
instance coproductEmbeddingRetraction_epi : Epi (coproductEmbeddingRetraction G e) :=
  epi_of_epi_fac (coproductEmbeddingSection_comp_retraction G e)

end SerrePositivity.KST.DerivedGeometry
