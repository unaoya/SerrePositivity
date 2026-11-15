module

public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorElementSelected
public import SerrePositivity.EInfinity.ComplexLimits.ConeWithoutFirst
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorConeObjects

/-!
# 元の全加群 frame 図式と選択 cochain を接合した cone データ

概要：M10 の同じ元の対象・通常単体・高次 cochain を接合する。
方針：始点を含む成分には符号つき選択 cochain、他には同じ通常単体を使う。
規約：HA Construction 1.3.1.6、全方程式は後続で検証する。
使われ方：同じ全評価屋根との比較に使う全 cone/prism の実データ。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Opposite SSet
open SerrePositivity.DifferentialGraded SerrePositivity.EInfinity.ComplexLimits
open ConeHeadIndex
open SerrePositivity.InfinityCategories.HA.Section7_1_1
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open scoped Simplicial
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

/-- 概要：元の probe を同じ全 frame 列の始点へ前置する。
方針：元の全通常加群の対象をそのまま使う。
規約：HA 1.3.1.6、元の対象。使われ方：実 cone の全頂点。 -/
def strictRawModuleTensorConeObj {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    Fin (n + 2) → RightModule A (dgAlgebraCategory A ((assocForget A).obj X)) :=
  Fin.cases (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P))
    (fun i => ForgetEnrichment.to (Complex A)
      ((strictRawModuleTensorElementDiagram A X P Q).obj (c.obj i)))

/-- 概要：同じ cone の先端は元の probe。
方針：同じ場合分けの零成分を読む。
規約：HA 1.3.1.6、同じ先端。使われ方：混合成分の型。 -/
lemma strictRawModuleTensorConeObj_zero {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    strictRawModuleTensorConeObj A X P Q c 0 =
      ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P) := rfl

/-- 概要：同じ cone の末尾頂点は元の全 frame 図式。
方針：同じ場合分けの後続成分を読む。
規約：HA 1.3.1.6、同じ頂点。使われ方：元の全通常単体の回収。 -/
lemma strictRawModuleTensorConeObj_succ {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) (i : Fin (n + 1)) :
    strictRawModuleTensorConeObj A X P Q c i.succ =
      ForgetEnrichment.to (Complex A)
        ((strictRawModuleTensorElementDiagram A X P Q).obj (c.obj i)) := rfl

/-- 概要：同じ零でない頂点を元の末尾次数で回収する。
方針：既存の末尾単調写像と同じ後続表示を使う。
規約：HA 1.3.1.6、同じ頂点。使われ方：全通常成分との接合。 -/
lemma strictRawModuleTensorConeObj_ne_zero {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (i : Fin (n + 2)) (hi : i ≠ 0) :
    strictRawModuleTensorConeObj A X P Q c i =
      ForgetEnrichment.to (Complex A)
        ((strictRawModuleTensorElementDiagram A X P Q).obj (c.obj (coneTailOrderHom n i))) := by
  obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.mpr hi
  rw [strictRawModuleTensorConeObj_succ, coneTailOrderHom_succ]

/-- 概要：元の frame 列を同じ dg nerve の通常単体として保持する。
方針：元の末尾写像の後に同じ全図式を合成する。
規約：HA 1.3.1.6、元の通常射。使われ方：始点を含まない cone 成分。 -/
def strictRawModuleTensorConeOrdinarySimplex {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    Simplex A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X))) (n + 1) :=
  closedNerveSimplex ((coneTailOrderHom n).monotone.functor ⋙ c ⋙
    strictRawModuleTensorElementDiagram A X P Q)

/-- 概要：同じ通常単体の対象は元の末尾 frame 対象。
方針：元の閉 nerve 単体の対象を読む。
規約：HA 1.3.1.6、同じ端点。使われ方：成分の型の移送。 -/
lemma strictRawModuleTensorConeOrdinarySimplex_obj {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) (i : Fin (n + 2)) :
    (strictRawModuleTensorConeOrdinarySimplex A X P Q c).obj i =
      ForgetEnrichment.to (Complex A)
        ((strictRawModuleTensorElementDiagram A X P Q).obj (c.obj (coneTailOrderHom n i))) := rfl

/-- 概要：元の通常成分と選択した高次 cochain を同じ実 cone データへ接合する。
方針：先端を含む成分を元の次数符号で移送し、他は同じ通常単体を保持する。
規約：HA 1.3.1.6、全方程式を仮定しない。使われ方：全 cone 方程式の検証対象。 -/
def strictRawModuleTensorConeData {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    SimplexData A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X))) (n + 1) where
  obj := strictRawModuleTensorConeObj A X P Q c
  hom I a b k hI ha hb hk := by
    have hab : a < b := by
      rw [ha, hb]
      exact I.min'_lt_max'_of_card (by omega)
    have hb0 : b ≠ 0 := ne_of_gt ((Fin.zero_le a).trans_lt hab)
    by_cases ha0 : a = 0
    · have h0 : (0 : Fin (n + 2)) ∈ I := by
        rw [← ha0, ha]
        exact I.min'_mem _
      have hJ := withoutFirst_nonempty hI h0
      have hc := card_withoutFirst I h0
      have hk' : k = 1 - ((withoutFirst I).card : ℤ) := by omega
      have hb' : b = ((withoutFirst I).max' hJ).succ :=
        hb.trans (max_withoutFirst I hI h0).symm
      exact cast (by rw [ha0, strictRawModuleTensorConeObj_zero, hb',
        strictRawModuleTensorConeObj_succ])
        (k.negOnePow •
          strictRawModuleTensorElementSelectedCochainAtMax A X P Q c (withoutFirst I) k hJ hk')
    · exact cast (by
        rw [strictRawModuleTensorConeOrdinarySimplex_obj, strictRawModuleTensorConeOrdinarySimplex_obj,
          strictRawModuleTensorConeObj_ne_zero A X P Q c a ha0,
          strictRawModuleTensorConeObj_ne_zero A X P Q c b hb0])
        ((strictRawModuleTensorConeOrdinarySimplex A X P Q c).toSimplexData.hom I a b k hI ha hb hk)

end SerrePositivity.EInfinity.BarrattEccles
