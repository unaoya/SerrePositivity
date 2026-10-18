module

public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapNaturality
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.Category.Preorder

/-!
概要：KST §3.1 の非空有限重なり全体の係数環図式。
方針：各非空有限集合で pivot を選び、制限と pivot 変更を合成して環射を定義する。
規約：添字は包含順序、環射は有限集合の拡大に沿って進む。
使われ方：有限 Čech 図式の係数環と、その上の Koszul dg 模型。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory

variable (R : Type u) [CommRing R] {I : Type v} [DecidableEq I]

/-- 概要：有限重なりの拡大と pivot 変更をまとめた環射。
方針：同じ pivot で制限した後、目標の pivot に変更する。
規約：KST §3.1。使われ方：非空有限重なり関手の射。 -/
def finiteOverlapChartMap (i k : I) {T U : Finset I} (h : T ⊆ U) (hi : i ∈ T) :
    FiniteOverlapRing R i T →ₐ[R] FiniteOverlapRing R k U :=
  (finiteOverlapPivotMap R k i U (h hi)).comp (finiteOverlapRestriction R i h)

/-- 概要：同じ集合・同じ pivot のまとめた環射は恒等。
方針：制限と pivot 変更の各恒等則を使う。
規約：KST §3.1。使われ方：重なり関手の恒等律。 -/
theorem finiteOverlapChartMap_refl (i : I) (T : Finset I) (hi : i ∈ T) :
    finiteOverlapChartMap R i i (Finset.Subset.refl T) hi =
      AlgHom.id R (FiniteOverlapRing R i T) := by
  rw [finiteOverlapChartMap, finiteOverlapPivotMap_self, finiteOverlapRestriction_refl]
  rfl

/-- 概要：有限重なりの拡大と pivot 変更をまとめた環射は合成を保つ。
方針：制限と pivot 変更の自然性、pivot の cocycle、制限の合成則を使う。
規約：KST §3.1。使われ方：全有限重なり関手の合成律。 -/
theorem finiteOverlapChartMap_comp (i k l : I) {T U V : Finset I}
    (h : T ⊆ U) (g : U ⊆ V) (hi : i ∈ T) (hk : k ∈ U) :
    (finiteOverlapChartMap R k l g hk).comp (finiteOverlapChartMap R i k h hi) =
      finiteOverlapChartMap R i l (h.trans g) hi := by
  apply AlgHom.ext
  intro z
  change finiteOverlapPivotMap R l k V (g hk)
      (finiteOverlapRestriction R k g
        (finiteOverlapPivotMap R k i U (h hi) (finiteOverlapRestriction R i h z))) = _
  have hn := AlgHom.congr_fun (finiteOverlapPivotMap_restriction R k i g (h hi))
    (finiteOverlapRestriction R i h z)
  change finiteOverlapRestriction R k g
      (finiteOverlapPivotMap R k i U (h hi) (finiteOverlapRestriction R i h z)) = _ at hn
  rw [hn]
  have hp := AlgHom.congr_fun (finiteOverlapPivotMap_cocycle R l k i V (g hk) (g (h hi)))
    (finiteOverlapRestriction R i g (finiteOverlapRestriction R i h z))
  have hr := AlgHom.congr_fun (finiteOverlapRestriction_comp R i h g) z
  exact hp.trans (congrArg (finiteOverlapPivotMap R l i V (g (h hi))) hr)

/-- 概要：非空有限重なりの添字型。
方針：有限集合の非空部分型を使う。
規約：KST §3.1、包含の順序圏。使われ方：係数環関手の添字。 -/
abbrev FiniteOverlapIndex (I : Type v) := {T : Finset I // T.Nonempty}

/-- 概要：非空有限重なりの表示に使う pivot。
方針：非空性から一つの元を選ぶ。
規約：KST §3.1、異なる選択は証明済みの pivot 比較で結ばれる。
使われ方：各添字での係数環の選択。 -/
def finiteOverlapIndexPivot (T : FiniteOverlapIndex I) : I := T.property.choose

omit [DecidableEq I] in
/-- 概要：選択した pivot は重なりの添字集合に属する。
方針：非空性の選択仕様。
規約：KST §3.1。使われ方：関手の射の定義と恒等・合成律。 -/
theorem finiteOverlapIndexPivot_mem (T : FiniteOverlapIndex I) :
    finiteOverlapIndexPivot T ∈ T.val := T.property.choose_spec

/-- 概要：非空有限重なりを可換 R 代数へ送る実際の関手。
方針：選択 pivot の局所化環と、証明済みのまとめた環射の関手性を束ねる。
規約：KST §3.1。使われ方：全有限 Čech の係数環図式。 -/
def finiteOverlapRingDiagram : FiniteOverlapIndex I ⥤ CommAlgCat.{max u v} R where
  obj T := CommAlgCat.of R (FiniteOverlapRing R (finiteOverlapIndexPivot T) T.val)
  map {T U} f := CommAlgCat.ofHom
    (finiteOverlapChartMap R (finiteOverlapIndexPivot T) (finiteOverlapIndexPivot U)
      (leOfHom f) (finiteOverlapIndexPivot_mem T))
  map_id T := by
    apply CommAlgCat.hom_ext
    change finiteOverlapChartMap R (finiteOverlapIndexPivot T) (finiteOverlapIndexPivot T)
      (Finset.Subset.refl T.val) (finiteOverlapIndexPivot_mem T) = AlgHom.id R _
    exact finiteOverlapChartMap_refl R _ T.val (finiteOverlapIndexPivot_mem T)
  map_comp {T U V} f g := by
    apply CommAlgCat.hom_ext
    exact (finiteOverlapChartMap_comp R _ _ _ (leOfHom f) (leOfHom g)
      (finiteOverlapIndexPivot_mem T) (finiteOverlapIndexPivot_mem U)).symm

end SerrePositivity.KST.DerivedBlowup
