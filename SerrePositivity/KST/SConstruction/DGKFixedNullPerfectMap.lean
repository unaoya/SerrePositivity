module
public import SerrePositivity.KST.SConstruction.DGKFixedNullPerfectZeroIso
public import SerrePositivity.KST.SConstruction.StableZeroTargetHom

/-!
概要：二つの実全対象商間の任意の固定 S 辺は、同じ Cat^perf ν 像で可逆となる。
方針：元零頂点の指定同型を合成し、元の辺の類を零終点の一意性で照合する。
規約：実辺を指定比較辺へ置換しない。使われ方：始域屋根の上零辺の全比較。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet DifferentialGraded InfinityCategories LocalizingInvariants
variable (R : Type u) [CommRing R] (A B : PerfDGInput.{u, v} R)

/-- 概要：元の二零商間の完全射の Cat^perf の射の類は可逆。
方針：同じ元の二零角の指定同型と零終点への射の一意性を使う。
規約：元全関手の辺の類。使われ方：実上零辺の可逆性。 -/
lemma dgKFixedNullPerfectHoMap_isIso
    (f : dgFixedNullInput R A ⟶ dgFixedNullInput R B) :
    IsIso (perfectStableHoArrow (dgKInputNuMap R f)
      (dgKInputStableValue_isIdempotentComplete R (dgFixedNullInput R A))
      (dgKInputStableValue_isIdempotentComplete R (dgFixedNullInput R B))) := by
  let e := (dgKFixedNullPerfectZeroIso R A).symm ≪≫ dgKFixedNullPerfectZeroIso R B
  have he : perfectStableHoArrow (dgKInputNuMap R f)
      (dgKInputStableValue_isIdempotentComplete R (dgFixedNullInput R A))
      (dgKInputStableValue_isIdempotentComplete R (dgFixedNullInput R B)) = e.hom :=
    perfectZeroVertexTarget_hom_ext
      (perfectStableVertex (dgKInputStableValue R (dgFixedNullInput R A))
        (dgKInputStableValue_isIdempotentComplete R (dgFixedNullInput R A)))
      (perfectStableVertex (dgKInputStableValue R (dgFixedNullInput R B))
        (dgKInputStableValue_isIdempotentComplete R (dgFixedNullInput R B)))
      (dgFixedNullInput_isZeroCategory R B) _ _
  rw [he]
  exact e.isIso_hom

/-- 概要：元の二零商間の固定 S 辺は同じ全一単体の ν 像で可逆。
方針：元 ν の全一単体回収式で射の類の可逆性を移す。
規約：選んだ代表へ置換しない。使われ方：実始域比較長方形の零頂点成分。 -/
lemma dgKFixedNullPerfectNuMap_isInvertible
    (f : dgFixedNullInput R A ⟶ dgFixedNullInput R B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).map (dgKInputPerfectNu R)).toTruncated := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e := ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).map
    (dgKInputPerfectNu R)).toTruncated) (f := (perfectStableArrow (dgKInputNuMap R f)
      (dgKInputStableValue_isIdempotentComplete R (dgFixedNullInput R A))
      (dgKInputStableValue_isIdempotentComplete R (dgFixedNullInput R B))).toTruncated)
    (dgKInputPerfectNu_edge R f)).mpr
  exact dgKFixedNullPerfectHoMap_isIso R A B f
end SerrePositivity.KST.SConstruction
