module

public import SerrePositivity.BhattScholze.Prism.Perfection.PrismPerfection
public import SerrePositivity.BhattScholze.Prism.Basic.Rigidity
public import SerrePositivity.BhattScholze.Prismatic.PrismOver

/-!
# prism の古典的な完全化

## 概要
任意の prism の δ 完全化を実 (p,d) 完備化し、標準射と完全 prism への普遍性を与える。
## 方針
既存の非完全な源からの δ 完全化の一意延長を、prism の射として用いる。
## 規約
BS 著者版 Lemma 3.9・Proposition 7.10。源の完全性を仮定しない。
## 使われ方
S′ 上の始的 prism の完全化と Corollary 7.3 の比較。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze
open CategoryTheory DerivedCompletion Prismatic
set_option backward.isDefEq.respectTransparency false
variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B]

/-- δ 完全化した環を、生成元と p に沿って実完備化した係数環。 -/
def classicalPrismPerfectionCoefficients (Q : OrientedPrism p B) : CommRingCat.{u} :=
  let b := deltaPerfectionOf Q.deltaStructure 0 Q.generator
  letI := pdCompletionCommRing (DeltaPerfection Q.deltaStructure) p b
  CommRingCat.of (PDCompletionH0 (DeltaPerfection Q.deltaStructure) p b)

/-- 実完備化後の標準完全 prism。 -/
def classicalPrismPerfection (Q : OrientedPrism p B) :
    OrientedPrism p (classicalPrismPerfectionCoefficients Q) :=
  perfectDeltaPDPrism (deltaPerfectionStructure Q.deltaStructure)
    (deltaPerfection_isPerfect Q.deltaStructure) (deltaPerfectionOf Q.deltaStructure 0 Q.generator)
    ((deltaPerfectionOf_isDeltaHom Q.deltaStructure 0).map_isDistinguished Q.isDistinguished_generator)

/-- 標準完全化の δ 構造は完全。 -/
theorem classicalPrismPerfection_isPerfect (Q : OrientedPrism p B) :
    (classicalPrismPerfection Q).deltaStructure.IsPerfect :=
  perfectDeltaPDPrism_isPerfect _ _ _ _

/-- 標準完全化は有界。剰余のねじれの指数は1。 -/
theorem classicalPrismPerfection_isBounded (Q : OrientedPrism p B) :
    IsBoundedPrism (classicalPrismPerfection Q) := by
  refine ⟨1, ?_⟩
  intro n x hx
  simpa only [pow_one] using (classicalPrismPerfection Q).quotient_p_pow_torsion_killed_by_p
    (classicalPrismPerfection_isPerfect Q) n x hx

/-- 元の prism から実完全化への標準 δ-prism 射。 -/
def classicalPrismPerfectionMap (Q : OrientedPrism p B) :
    OrientedPrism.Hom Q (classicalPrismPerfection Q) := by
  letI := pdCompletionCommRing (DeltaPerfection Q.deltaStructure) p
    (deltaPerfectionOf Q.deltaStructure 0 Q.generator)
  exact {
  toRingHom := (pdCompletionUnit _ p (deltaPerfectionOf Q.deltaStructure 0 Q.generator)).comp
    (deltaPerfectionOf Q.deltaStructure 0)
  map_delta := (pdCompletionUnit_isDeltaHom _ _).comp (deltaPerfectionOf_isDeltaHom _ 0)
  ideal_le := by
    rw [OrientedPrism.ideal, Ideal.span_singleton_le_iff_mem]
    change (classicalPrismPerfection Q).generator ∈ (classicalPrismPerfection Q).ideal
    exact Ideal.mem_span_singleton_self _ }

/-- 標準完全化の生成元は元の選択生成元の標準像。 -/
theorem classicalPrismPerfectionMap_generator (Q : OrientedPrism p B) :
    (classicalPrismPerfectionMap Q).toRingHom Q.generator = (classicalPrismPerfection Q).generator := rfl

/-- 概要：非完全な源の prism 射は、標準完全化から完全標的へ一意に延長する。
方針：非完全な δ 源からの実完全化普遍性と、生成元の像の完備性を使う。
規約：BS 著者版 Lemma 3.9・Proposition 7.10。標的の完全性のみを要求。
使われ方：S′ 上の始性を完全試験 prism へ移す。 -/
theorem existsUnique_classicalPrismPerfectionHom (Q : OrientedPrism p B)
    {C : Type u} [CommRing C] (Y : OrientedPrism p C) (hY : Y.deltaStructure.IsPerfect)
    (f : OrientedPrism.Hom Q Y) :
    ∃! g : OrientedPrism.Hom (classicalPrismPerfection Q) Y,
      g.comp (classicalPrismPerfectionMap Q) = f := by
  obtain ⟨g, hg, hgu⟩ := existsUnique_deltaPerfectionPDCompletionHom Q.deltaStructure Q.generator
    Y.deltaStructure hY f.toRingHom f.map_delta Y.complete_p f.isModuleComplete_map_generator
  have hgf : g.comp (classicalPrismPerfectionMap Q).toRingHom = f.toRingHom := hg.2
  let G : OrientedPrism.Hom (classicalPrismPerfection Q) Y := ⟨g, hg.1, by
    rw [OrientedPrism.ideal, Ideal.span_singleton_le_iff_mem]
    change (g.comp (classicalPrismPerfectionMap Q).toRingHom) Q.generator ∈ Y.ideal
    rw [hgf]
    exact f.map_generator_mem⟩
  refine ⟨G, ?_, ?_⟩
  · apply OrientedPrism.Hom.ext
    exact hg.2
  · intro k hk
    apply OrientedPrism.Hom.ext
    apply hgu
    exact ⟨k.map_delta, congrArg OrientedPrism.Hom.toRingHom hk⟩

end SerrePositivity.BhattScholze
