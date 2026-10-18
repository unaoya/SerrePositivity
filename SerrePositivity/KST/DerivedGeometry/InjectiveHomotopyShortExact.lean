module

public import SerrePositivity.KST.DerivedGeometry.InjectiveHomotopyExtension
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
概要：各項 injective な複体への零ホモトピー直交性は短完全列の両端から中央へ移る。
方針：第一項上の零ホモトピーを延長し、差を余核へ降ろす。
規約：同次成分の延長の存在も実際に証明済みの補題を用いる。
使われ方：Stacks Lemma 19.12.3 (079L)、TT §3・§8、Toën §3.2 の超限判定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits
namespace SerrePositivity.KST.DerivedGeometry
variable {C : Type*} [Category* C] [Abelian C]
  (S : ShortComplex (CochainComplex C ℤ)) (hS : S.ShortExact)
  (I : CochainComplex C ℤ) [∀ n, Injective (I.X n)]

include hS

/--
概要：短完全列の両端からの全射が零ホモトピーなら、中央からの全射も零ホモトピー。
方針：部分複体での零ホモトピーを延長し、余核の普遍性で残差を降ろして合成する。
規約：非有界複体に対する主張。
使われ方：Stacks 19.12.3、TT §3 の小さい非輪状商を加える工程。
-/
lemma homotopy_orthogonal_of_shortExact
    (h₁ : ∀ f : S.X₁ ⟶ I, Nonempty (Homotopy f 0))
    (h₃ : ∀ f : S.X₃ ⟶ I, Nonempty (Homotopy f 0))
    (f : S.X₂ ⟶ I) : Nonempty (Homotopy f 0) := by
  have := hS.mono_f
  have := hS.epi_g
  obtain ⟨g, hfg, hg⟩ := exists_nullHomotopic_extension S.f (h₁ (S.f ≫ f)).some
  have hz : S.f ≫ (f - g) = 0 := by
    rw [Preadditive.comp_sub, hfg, sub_self]
  let d : S.X₃ ⟶ I := hS.exact.desc (f - g) hz
  have hd : S.g ≫ d = f - g := hS.exact.g_desc _ hz
  have ht : Homotopy (f - g) 0 := by
    simpa only [hd, comp_zero] using (h₃ d).some.compLeft S.g
  have hh := ht.add hg.some
  exact ⟨by simpa only [sub_add_cancel, add_zero] using hh⟩

end SerrePositivity.KST.DerivedGeometry
