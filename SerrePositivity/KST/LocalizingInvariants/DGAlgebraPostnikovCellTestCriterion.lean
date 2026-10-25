module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraQuasiIsoInfinityVertices
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovInfinityCone
public import SerrePositivity.InfinityCategories.F1.Yoneda.RepresentableLimitCharacterization
public import SerrePositivity.InfinityCategories.F2.Compact.HomCovariantComparison
public import SerrePositivity.InfinityCategories.F1.Categories.OppositeFunctorIso
public import SerrePositivity.InfinityCategories.Core.UniverseEdgeTransport

/-!
概要：元の局所化 Postnikov 錐の極限性は、実 cell 像を源とする表現可能試験で検出する。
方針：全局所化頂点の cell 像表示と、元の全共同 Hom の第一変数自然性を使う。
規約：試験錐の極限性はまだ証明せず、導来写像模型との比較を追加入力で代替しない。
使われ方：実 cell 写像模型との全自然比較を適用する正確な極限判定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (B : Mon (Complex R)) [B.X.IsStrictlyLE 0]
  (n : ℤ) (hn : 0 ≤ n)

lemma postnikovInfinityCone_isLimit_iff_cellTests :
    IsLimitCone (postnikovInfinityCone R B n hn) ↔
      ∀ A : Mon (Complex R), IsLimitCone
        (mapJoinCone (covariantRepresentableInfinity
          (quasiIsoInfinityVertex R (cellResolution R A)))
          (JoinCone.ulift.{u + 1, u + 2} (postnikovInfinityCone R B n hn))) := by
  constructor
  · intro hc A
    exact covariantRepresentableInfinity_isLimit _ hc _
  · intro hc
    apply isLimitCone_of_covariantRepresentableInfinity
    intro x
    obtain ⟨A, ⟨e⟩⟩ := exists_cellResolutionInfinityVertexIso R x
    let eu : VertexIso
        (X := SSet.uliftFunctor.{u + 2, u + 1}.obj (quasiIsoInfinity R).op)
        (ULift.up (SSet.opObjEquiv.symm (quasiIsoInfinityVertex R (cellResolution R A))))
        (ULift.up (SSet.opObjEquiv.symm x)) :=
      (UniverseEdge.upFunctor.{u + 1, u + 2} (quasiIsoInfinity R).op).mapIso (VertexIso.op e)
    have eh : FunctorIso (homInfinityCovariant
        (quasiIsoInfinityVertex R (cellResolution R A))) (homInfinityCovariant x) := by
      have he := VertexIso.map eu (coyonedaInfinityMap (quasiIsoInfinity R))
      simpa only [coyonedaInfinityMap_vertex] using he
    let ec : FunctorIso (covariantRepresentableInfinity
        (quasiIsoInfinityVertex R (cellResolution R A))) (covariantRepresentableInfinity x) :=
      (F2.Compact.homInfinityCovariant_covariantIso _).symm ≪≫ eh ≪≫
        F2.Compact.homInfinityCovariant_covariantIso _
    exact (hc A).of_functorIso (FunctorIso.precomp ec
      (JoinCone.ulift.{u + 1, u + 2} (postnikovInfinityCone R B n hn)).val)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
