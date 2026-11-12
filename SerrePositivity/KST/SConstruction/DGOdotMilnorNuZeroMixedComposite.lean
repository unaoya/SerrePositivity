module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNuZeroMixedEdges

/-!
概要：指定零角成分を保つ元混合二辺を同じ零成分内で実三角形として合成する。
方針：既存の辺表示と合成三角形の実現を同じ可縮零成分へ適用する。
規約：元混合二辺と同じ中間頂点を固定。使われ方：上二胞体比較の合成境界。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R) (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d)

/-- 概要：元混合二辺の同じ実合成辺と指定合成三角形。
方針：同じ合成の辺代表を取り、元二辺を保つ実二単体を回収する。
規約：二辺を選び直さない。使われ方：零角成分を保つ上混合境界の固定。 -/
def dgOdotMilnorNuZeroMixedCompositeData :
    Σ e : (DGOdotMilnorNuNullCoherenceSpace R d).Edge
      (dgOdotMilnorNuZeroMixedStart R d) (dgOdotMilnorNuZeroMixedTarget R d),
      SSet.Edge.CompStruct (dgOdotMilnorNuZeroMixedLeftEdge R d)
        (dgOdotMilnorNuZeroMixedTopEdge R d) e := by
  letI : KanComplex (DGOdotMilnorNuNullCoherenceSpace R d) :=
    (dgOdotMilnorNuNullCoherenceSpace_contractible R d h).kanComplex
  let hex := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective
    (X := DGOdotMilnorNuNullCoherenceSpace R d) _ _
      (SSet.Truncated.HomotopyCategory.homMk (dgOdotMilnorNuZeroMixedLeftEdge R d).toTruncated ≫
        SSet.Truncated.HomotopyCategory.homMk (dgOdotMilnorNuZeroMixedTopEdge R d).toTruncated)
  let e := hex.choose
  have he := hex.choose_spec
  exact ⟨Edge.ofTruncated e,
    SSet.Edge.CompStruct.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.compStruct_nonempty_of_homMk_fac he.symm).some⟩

/-- 概要：元の二混合辺の同じ選択合成辺。
方針：同じ実合成三角形に属する辺を読む。
規約：元二辺と指定中間頂点を保持。使われ方：零 Hom 比較正方形の上側合成境界。 -/
def dgOdotMilnorNuZeroMixedCompositeEdge :
    (DGOdotMilnorNuNullCoherenceSpace R d).Edge
      (dgOdotMilnorNuZeroMixedStart R d) (dgOdotMilnorNuZeroMixedTarget R d) :=
  (dgOdotMilnorNuZeroMixedCompositeData R d h).1

/-- 概要：同じ合成辺は元の指定二混合辺と実二単体をなす。
方針：選択した同じ実合成データの元二単体を読む。
規約：ホモトピー圏の合成等号だけに弱めない。使われ方：元零角成分の二面保持。 -/
def dgOdotMilnorNuZeroMixedCompositeTriangle :
    SSet.Edge.CompStruct (dgOdotMilnorNuZeroMixedLeftEdge R d)
      (dgOdotMilnorNuZeroMixedTopEdge R d) (dgOdotMilnorNuZeroMixedCompositeEdge R d h) :=
  (dgOdotMilnorNuZeroMixedCompositeData R d h).2

end SerrePositivity.KST.SConstruction
