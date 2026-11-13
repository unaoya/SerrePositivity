module

public import SerrePositivity.BhattScholze.Prism.Perfectoid.PerfectPrismHomLift

/-!
# 剰余の単位を指定した始性と環同型

## 概要
試験 prism への一意な射という始性を、元の環の同型で移す。
## 方針
剰余射を同型と逆同型で合成し、元ごとに両逆を使う。
## 規約
指定された単位を保つ。一意な射の存在だけに弱めない。
## 使われ方
BS 著者版 Proposition 7.10 の完備化・添字の比較。
-/

public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Semiperfectoid
set_option backward.isDefEq.respectTransparency false
variable {p : ℕ} [Fact p.Prime] {S T B C : Type u}
  [CommRing S] [CommRing T] [CommRing B] [CommRing C]

/-- 単位を指定した試験 prism への始性を、源の環同型で移す。 -/
theorem existsUnique_prismHom_of_source_equiv
    (Q : OrientedPrism p B) (Y : OrientedPrism p C)
    (v : S →+* B ⧸ Q.ideal) (e : T ≃+* S)
    (h : ∀ s : S →+* C ⧸ Y.ideal, ∃! g : OrientedPrism.Hom Q Y,
      g.quotientMap.comp v = s) (s : T →+* C ⧸ Y.ideal) :
    ∃! g : OrientedPrism.Hom Q Y, g.quotientMap.comp (v.comp e.toRingHom) = s := by
  obtain ⟨g, hg, hgu⟩ := h (s.comp e.symm.toRingHom)
  refine ⟨g, ?_, ?_⟩
  · apply RingHom.ext
    intro x
    exact (RingHom.congr_fun hg (e x)).trans (congrArg s (e.symm_apply_apply x))
  · intro g' hg'
    apply hgu
    apply RingHom.ext
    intro x
    have he := RingHom.congr_fun hg' (e.symm x)
    change g'.quotientMap (v (e (e.symm x))) = s (e.symm x) at he
    change g'.quotientMap (v x) = s (e.symm x)
    simpa only [e.apply_symm_apply] using he

end SerrePositivity.BhattScholze.Semiperfectoid
