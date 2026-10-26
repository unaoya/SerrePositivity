module
public import SerrePositivity.KST.SConstruction.DGKPerfectNuEquivalence
public import SerrePositivity.InfinityCategories.Derived.ArrowIsoFromCommutingEdges

/-!
概要：完全射の全自然な可換比較を、Cat^perf 内の区間図式全体の比較へ運ぶ。
方針：同じ射の類の合成則で可換式を回収し、指定可逆二成分で実区間を比較する。
規約：全関手同型を保持し、Verdier 商や局所化の新しい API は作らない。
使われ方：D2 の全対角・全 cone 比較から実右面の指定辺比較を構成する。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet InfinityCategories LocalizingInvariants F2.Idempotent
open scoped Simplicial
variable {A B C D : StableCategory.{u}}
  (f : ExactMap A B) (g : ExactMap C D) (a : ExactMap A C) (b : ExactMap B D)
  (hA : IsIdempotentComplete A.obj) (hB : IsIdempotentComplete B.obj)
  (hC : IsIdempotentComplete C.obj) (hD : IsIdempotentComplete D.obj)
  (e : FunctorIso (f.hom ≫ b.hom) (a.hom ≫ g.hom))
include e

/-- 概要：完全射の全自然比較は同じ Cat^perf 射の四辺可換式を与える。
方針：同じ完全合成の類と全関手同型不変性を使う。
規約：元四射を保持。使われ方：区間全比較の指定端点可換条件。 -/
lemma perfectStableHoArrow_square_eq_of_functorIso :
    perfectStableHoArrow f hA hB ≫ perfectStableHoArrow b hB hD =
      perfectStableHoArrow a hA hC ≫ perfectStableHoArrow g hC hD := by
  let F : ExactMap A D := ⟨f.hom ≫ b.hom,
    @isExactFunctor_comp _ _ _ _ _ f.isExact b.isExact⟩
  let G : ExactMap A D := ⟨a.hom ≫ g.hom,
    @isExactFunctor_comp _ _ _ _ _ a.isExact g.isExact⟩
  have hf : perfectStableHoArrow F hA hD =
      perfectStableHoArrow f hA hB ≫ perfectStableHoArrow b hB hD :=
    perfectStableHoArrow_comp f b hA hB hD
  have hg : perfectStableHoArrow G hA hD =
      perfectStableHoArrow a hA hC ≫ perfectStableHoArrow g hC hD :=
    perfectStableHoArrow_comp a g hA hC hD
  have he : perfectStableHoArrow F hA hD = perfectStableHoArrow G hA hD :=
    perfectStableHoArrow_eq_of_functorIso (F := F) (G := G) hA hD e
  exact hf.symm.trans (he.trans hg)

/-- 概要：全自然な可換比較と可逆二成分から、元 Cat^perf 辺の区間全比較を構成できる。
方針：同じ四辺可換式を既存の区間全比較の存在定理へ渡す。
規約：端点だけの同型ではない。使われ方：実右面の包含・商境界の指定比較。 -/
lemma nonempty_perfectStableArrowFunctorIso_of_equivalences
    (ha : IsQCatEquivalence a.hom) (hb : IsQCatEquivalence b.hom) :
    Nonempty (FunctorIso (SSet.yonedaEquiv.symm (perfectStableArrow f hA hB).edge)
      (SSet.yonedaEquiv.symm (perfectStableArrow g hC hD).edge)) := by
  apply nonempty_arrowFunctorIso_of_comm
    (perfectStableArrow f hA hB).toTruncated (perfectStableArrow g hC hD).toTruncated
    (perfectStableArrow a hA hC).toTruncated (perfectStableArrow b hB hD).toTruncated
  · exact perfectStableHoArrow_isIso_of_isQCatEquivalence a hA hC ha
  · exact perfectStableHoArrow_isIso_of_isQCatEquivalence b hB hD hb
  · exact perfectStableHoArrow_square_eq_of_functorIso f g a b hA hB hC hD e
end SerrePositivity.KST.SConstruction
