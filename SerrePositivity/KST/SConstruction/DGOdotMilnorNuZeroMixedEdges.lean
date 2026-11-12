module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNuStandardZeroNullHom

/-!
概要：指定零角成分を保つ二つの実混合 Hom 辺を同じ零成分で貼る。
方針：元左辺比較を元上辺で後合成し、元上辺比較を元 toZeroCategory で前合成する。
規約：同じ指定 fromZeroCategory 成分と元二辺。使われ方：上二胞体の混合合成境界。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "K" => dgKInputStableValue R (dgOdotMilnorFlatKernelInput R d)
local notation "B" => dgKInputStableValue R (dgOdotMilnorResolvedInput R d)
local notation "Z" => dgKInputStableValue R
  (dgFixedNullInput R (dgOdotMilnorFlatKernelInput R d))

/-- 概要：元実左辺と元実上辺を経由する混合辺の始点。
方針：実零角経由の全因子分解に元実左辺の頂点を入れる。
規約：元実合成を保持。使われ方：上混合合成辺の始点。 -/
def dgOdotMilnorNuZeroMixedStart : DGOdotMilnorNuNullCoherenceSpace R d _⦋0⦌ :=
  (dgOdotMilnorNuZeroCornerNullFactor R d).app (Opposite.op ⦋0⦌)
    (SimplicialCategory.homEquiv' (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}) (K) (Z)
      (dgOdotMilnorNuZeroActualLeft R d))

/-- 概要：同じ指定零角成分を挟む混合二辺の中間頂点。
方針：元上辺比較の始点を標準零角経由の全因子分解で写す。
規約：指定成分と元上辺を保持。使われ方：混合二辺の厳密貼り合わせ。 -/
def dgOdotMilnorNuZeroMixedMiddle : DGOdotMilnorNuNullCoherenceSpace R d _⦋0⦌ :=
  (dgOdotMilnorNuStandardZeroNullFactor R d).app (Opposite.op ⦋0⦌)
    (SimplicialCategory.homEquiv' (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}) _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroCategory.{u + 1} (B)
      (dgOdotMilnorNuZeroComparisonTop R d))

/-- 概要：元の標準零角を経由する混合辺の終点。
方針：元絶対上辺を同じ標準零角経由の全因子分解で写す。
規約：元核と元標準零角。使われ方：上混合合成辺の終点。 -/
def dgOdotMilnorNuZeroMixedTarget : DGOdotMilnorNuNullCoherenceSpace R d _⦋0⦌ :=
  (dgOdotMilnorNuStandardZeroNullFactor R d).app (Opposite.op ⦋0⦌)
    (SimplicialCategory.homEquiv' (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}) _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroCategory.{u + 1} (B)
      (fromZeroCategory (B)))

/-- 概要：指定零角成分を挟む二つの混合合成の中間頂点は厳密に同じ。
方針：同じ三完全射の基礎写像の結合則で全関手頂点を照合する。
規約：比較辺を追加しない。使われ方：指定混合二辺の厳密合成。 -/
lemma dgOdotMilnorNuZeroMixedMiddle_eq :
    (dgOdotMilnorNuZeroCornerNullFactor R d).app (Opposite.op ⦋0⦌)
        (SimplicialCategory.homEquiv' (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}) (K) (Z)
          (dgOdotMilnorNuZeroComparisonLeft R d)) = dgOdotMilnorNuZeroMixedMiddle R d := by
  apply Subtype.ext
  let f : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (K) (B) :=
    ⟨(dgOdotMilnorNuZeroComparisonLeft R d).hom ≫ (dgOdotMilnorNuZeroActualTop R d).hom,
      @_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.isExactFunctor_comp _ _ _ _ _ (dgOdotMilnorNuZeroComparisonLeft R d).isExact
        (dgOdotMilnorNuZeroActualTop R d).isExact⟩
  have hl : ((dgOdotMilnorNuZeroCornerNullFactor R d).app (Opposite.op ⦋0⦌)
      (SimplicialCategory.homEquiv' (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}) (K) (Z)
        (dgOdotMilnorNuZeroComparisonLeft R d))).val = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctorVertexEquiv (K) (B) f := by
    rfl
  have hr : (dgOdotMilnorNuZeroMixedMiddle R d).val = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctorVertexEquiv (K) (B)
      (dgOdotMilnorNuStandardZeroComposite R d (dgOdotMilnorNuZeroComparisonTop R d)) :=
    dgOdotMilnorNuStandardZeroNullHom_vertex R d (dgOdotMilnorNuZeroComparisonTop R d)
  have hf : f =
      dgOdotMilnorNuStandardZeroComposite R d (dgOdotMilnorNuZeroComparisonTop R d) := by
    apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap.ext
    exact Category.assoc (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.toZeroCategory (K)).hom (fromZeroCategory (Z)).hom
      (dgOdotMilnorNuZeroActualTop R d).hom
  exact hl.trans ((congrArg (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctorVertexEquiv (K) (B)) hf).trans hr.symm)

/-- 概要：元左辺比較の同じ実上辺による後合成の実零 Hom 辺。
方針：実零角経由の全因子分解で元 Hom 辺を写す。
規約：元比較辺と元上辺を保持。使われ方：上混合合成の第一辺。 -/
def dgOdotMilnorNuZeroMixedLeftEdge :
    (DGOdotMilnorNuNullCoherenceSpace R d).Edge
      (dgOdotMilnorNuZeroMixedStart R d) (dgOdotMilnorNuZeroMixedMiddle R d) :=
  ((dgOdotMilnorNuZeroComparisonLeftEdge R d).map
    (dgOdotMilnorNuZeroCornerNullFactor R d)).ofEq rfl (dgOdotMilnorNuZeroMixedMiddle_eq R d)

/-- 概要：元上辺比較の同じ元 toZeroCategory による前合成の実零 Hom 辺。
方針：標準零角経由の全因子分解で元 Hom 辺を写す。
規約：元比較辺と元零角成分を保持。使われ方：上混合合成の第二辺。 -/
def dgOdotMilnorNuZeroMixedTopEdge :
    (DGOdotMilnorNuNullCoherenceSpace R d).Edge
      (dgOdotMilnorNuZeroMixedMiddle R d) (dgOdotMilnorNuZeroMixedTarget R d) :=
  (dgOdotMilnorNuZeroComparisonTopEdge R d).map (dgOdotMilnorNuStandardZeroNullFactor R d)

end SerrePositivity.KST.SConstruction
