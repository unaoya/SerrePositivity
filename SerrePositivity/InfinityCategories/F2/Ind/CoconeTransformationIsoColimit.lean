module

public import SerrePositivity.InfinityCategories.F2.CoconeTransformationEquivalence
public import SerrePositivity.InfinityCategories.F2.CoconeTransformationPoint
public import SerrePositivity.InfinityCategories.Stable.InitialTransport

/-!
概要：同じ図式・指定頂点で標準変換が同型なら、元の native 余錐の余極限性を移せる。
方針：標準変換比較の充満忠実性で同じ終点固定余錐空間へ同型を戻し、全余錐空間へ含める。
規約：元の全余錐を固定。使われ方：指定単位の類を保持する相対 join 実現の係数比較。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 同じ指定頂点での標準変換の同型は、元の同じ二つの native 余錐の余極限性を移す。 -/
lemma isColimitCone_of_coconeTransformationIso {K X : SSet.{u}} [Quasicategory X]
    {f : K ⟶ X} (c d : JoinCocone f) (z : X _⦋0⦌)
    (hc : c.vertex = z) (hd : d.vertex = z)
    (e : VertexIso
      ((F2.coconeTransformationMap f z).app (Opposite.op ⦋0⦌) (F2.coconeMappingPointAt c z hc))
      ((F2.coconeTransformationMap f z).app (Opposite.op ⦋0⦌) (F2.coconeMappingPointAt d z hd)))
    (hcol : IsColimitCone c) : IsColimitCone d := by
  let he := (F2.coconeTransformationMap_isQCatEquivalence f z).isFullyFaithful.preimageVertexIso e
  exact hcol.of_vertexIso (he.map (vertexFiberι (sliceUnderProjection f) z))

end SerrePositivity.InfinityCategories.F2.Ind
