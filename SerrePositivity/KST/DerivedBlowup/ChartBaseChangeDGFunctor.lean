module

public import SerrePositivity.KST.DerivedBlowup.FreeKoszulBaseChange
public import SerrePositivity.KST.DerivedBlowup.ChartComplexes

/-!
概要：KST Def3.1 の標準チャート dg 圏とその底変更比較。
方針：チャート関係式の自由 Koszul 底変更と、像の微分の同定を合成する。
規約：同定する微分の間は恒等生成元写像を持つ dg 関手で結ぶ。
使われ方：チャート環射と実際の重なりでの dg 圏の比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory

variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B] {r : ℕ}

/-- 概要：標準チャートの自由生成元の微分係数の族。
方針：pivot を除く各添字に関係式 a_i S_j−a_j を置く。
規約：KST Def3.1。使われ方：自由 Koszul 底変更の入力。 -/
abbrev chartRelationFamily (a : Fin (r + 1) → R) (i : Fin (r + 1)) :
    ChartIndex i → ChartRing R i := fun j => chartRelation R a i j.val

/-- 概要：導来 blowup 標準チャートの一対象 dg 圏の対象型。
方針：チャート関係式の自由 Koszul 微分を対象型の添字に保持する。
規約：KST Def3.1。使われ方：チャート図式の局所 dg 圏。 -/
abbrev DerivedChartObject (a : Fin (r + 1) → R) (i : Fin (r + 1)) :=
  ExteriorKoszulObject (Finsupp.linearCombination (ChartRing R i) (chartRelationFamily a i))

/-- 概要：チャート底変更後の微分と像の関係式の線形結合微分は等しい。
方針：自由生成元上で係数と積・差の保存を使う。
規約：KST Def3.1。使われ方：底変更 dg 関手の終域の同定。 -/
theorem chartBaseChangeDifferential_id (a : Fin (r + 1) → R) (i : Fin (r + 1))
    (f : ChartRing R i →ₐ[R] B) :
    (chartKoszulDifferential (fun j => algebraMap R B (a j))
      (fun j => f (chartCoordinate R i j)) i).comp LinearMap.id =
      Finsupp.linearCombination B (f ∘ chartRelationFamily a i) := by
  apply Finsupp.lhom_ext
  intro j c
  simp [chartKoszulDifferential, chartRelationFamily, chartRelation]

/-- 概要：標準チャート dg 圏の係数変更を像の関係式のチャート dg 圏へ送る関手。
方針：自由 Koszul 底変更の後に恒等生成元で微分の同定を行う。
規約：KST Def3.1、既存 DGBaseChange を用いる。
使われ方：チャート環射の dg スカラー拡大比較。 -/
def chartBaseChangeDGFunctor (a : Fin (r + 1) → R) (i : Fin (r + 1))
    (f : ChartRing R i →ₐ[R] B) :
    EnrichedFunctor (DifferentialGraded.Complex B)
      (DifferentialGraded.ScalarExtension.DGBaseChange f.toRingHom (DerivedChartObject a i))
      (ExteriorKoszulObject (chartKoszulDifferential (fun j => algebraMap R B (a j))
        (fun j => f (chartCoordinate R i j)) i)) :=
  EnrichedFunctor.comp (DifferentialGraded.Complex B)
    (freeKoszulBaseChangeDGFunctor f.toRingHom (chartRelationFamily a i))
    (exteriorKoszulDGFunctor LinearMap.id
      (Finsupp.linearCombination B (f ∘ chartRelationFamily a i))
      (chartKoszulDifferential (fun j => algebraMap R B (a j))
        (fun j => f (chartCoordinate R i j)) i)
      (chartBaseChangeDifferential_id a i f))

/-- 概要：チャート dg 底変更関手の Hom 写像は複体同型。
方針：自由 Koszul 底変更と恒等線形同型の外積の合成を使う。
規約：KST Def3.1。使われ方：局所 dg 同値性。 -/
theorem chartBaseChangeDGFunctor_map_isIso (a : Fin (r + 1) → R) (i : Fin (r + 1))
    (f : ChartRing R i →ₐ[R] B) (x y) :
    IsIso ((chartBaseChangeDGFunctor a i f).map x y) := by
  have := freeKoszulBaseChangeDGFunctor_map_isIso f.toRingHom (chartRelationFamily a i) x y
  change IsIso ((freeKoszulBaseChangeDGFunctor f.toRingHom (chartRelationFamily a i)).map x y ≫
    (exteriorKoszulCochainIso (LinearEquiv.refl B _)
      (Finsupp.linearCombination B (f ∘ chartRelationFamily a i))
      (chartKoszulDifferential (fun j => algebraMap R B (a j))
        (fun j => f (chartCoordinate R i j)) i)
      (chartBaseChangeDifferential_id a i f)).hom)
  infer_instance

/-- 概要：標準チャート dg 圏の底変更比較は準同値。
方針：Hom 同型と一対象の H⁰ 上の全射性を使う。
規約：KST Def3.1。使われ方：重なり上のチャートの局所比較。 -/
theorem chartBaseChangeDGFunctor_quasiEquivalence (a : Fin (r + 1) → R)
    (i : Fin (r + 1)) (f : ChartRing R i →ₐ[R] B) :
    DifferentialGraded.QuasiEquivalence (chartBaseChangeDGFunctor a i f) := by
  constructor
  · intro x y
    have := chartBaseChangeDGFunctor_map_isIso a i f x y
    infer_instance
  · apply Functor.essSurj_of_surj
    rintro ⟨y⟩
    change ExteriorKoszulObject (chartKoszulDifferential (fun j => algebraMap R B (a j))
      (fun j => f (chartCoordinate R i j)) i) at y
    cases y
    exact ⟨⟨ExteriorKoszulObject.point⟩, rfl⟩

end SerrePositivity.KST.DerivedBlowup
