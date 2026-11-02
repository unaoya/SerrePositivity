module
public import SerrePositivity.KST.SConstruction.DGSmallPerfectEnvelope
public import SerrePositivity.DifferentialGraded.Functor.DGFunctorCoherence

/-!
概要：指定像を含む小さい Perf 包絡へ、同じ実 dg 関手を厳密に持ち上げる。
方針：指定族への所属と同じ対象・全 Hom 作用を保持し、包含回収を抽象関手で証明する。
規約：同型な代表の選択なし。使われ方：実逆回転の二つの関手像を共通小模型へ入れる。
-/
@[expose] public section
noncomputable section
universe u v w z
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (E : Type v) [DGCategory R E] [Small.{u} E]
  (J : Type w) (X : J → PerfectDGModule R E) {P : Type z} [DGCategory R P]
  (F : DGFunctor R P (PerfectDGModule R E)) (i : P → J)
  (h : ∀ a, X (i a) = F.obj a)

/-- 概要：元全像が指定族に属する同じ関手を共通小模型へ持ち上げる。
方針：元対象の所属証明と元 Hom 写像をそのまま使う。
規約：対象と全 Hom を保持。使われ方：実逆回転の二成分の厳密な制限。 -/
def dgSmallPerfectEnvelopeFunctorLift : DGFunctor R P (DGSmallPerfectEnvelope R E J X) where
  obj a := ⟨F.obj a, Or.inr (Or.inl ⟨i a, h a⟩)⟩
  map a b := F.map a b
  map_id a := F.map_id a
  map_comp a b c := F.map_comp a b c

/-- 概要：同じ持ち上げの Hom 写像は元関手の全 Hom 写像そのもの。
方針：元の定義を回収する。規約：全次数を保持。
使われ方：具体的な長い cone 関手を展開せず自然性を検証する。 -/
lemma dgSmallPerfectEnvelopeFunctorLift_map (a b : P) :
    (dgSmallPerfectEnvelopeFunctorLift R E J X F i h).map a b = F.map a b := rfl

/-- 概要：同じ持ち上げを含めると元の全 dg 関手を厳密回収する。
方針：抽象関手の同じ対象と全 Hom を比較する。
規約：元関手を展開しない。使われ方：具体的 cone 関手での包含回収。 -/
lemma dgSmallPerfectEnvelopeFunctorLift_inclusion :
    (dgSmallPerfectEnvelopeFunctorLift R E J X F i h).comp
      (dgSmallPerfectEnvelopeInclusion R E J X) = F := by
  apply EnrichedFunctor.ext (Complex R) (fun _ => rfl)
  intro a b
  change F.map a b ≫ 𝟙 _ = F.map a b
  exact Category.comp_id _
end SerrePositivity.KST.SConstruction
