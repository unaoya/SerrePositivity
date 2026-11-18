module

public import SerrePositivity.InfinityCategories.Sheaves.DiscretePresheafPushoutCocones
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.Cocone

/-!
概要：離散前層の本質像を drafts と同じ型で固定し、同じ押し出し図式の余極限へ移す。
方針：全余錐の比較から得た頂点同型を本質像の証人へ合成する。
  文献対応：HTT 5.5.6.28・6.2.2.7、Kerodon §4.4（Tag 01EM）、S8-2・3。
規約：前層を離散表示に等しいと要求せず、指定した頂点同型を保持する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C]

/-- 離散前層の埋め込みの本質像。HTT 5.5.6.28、Kerodon §3.1（Tag 00SZ）。
型は drafts/Sheaves/SpaceValued の Is0Truncated と同じ。 -/
def Is0Truncated (x : (PresheafCat C SpaceInfinity.{u}) _⦋0⦌) : Prop :=
  ∃ P : Cᵒᵖ ⥤ Type u, Nonempty (VertexIso x (functorVertex (discretePresheaf P)))

/-- 元の離散表示はその本質像に属する。HTT 5.5.6.28、Kerodon §3.1（Tag 00SZ）。 -/
lemma is0Truncated_discretePresheaf (P : Cᵒᵖ ⥤ Type u) :
    Is0Truncated (functorVertex (discretePresheaf P)) := ⟨P, ⟨Iso.refl _⟩⟩

/-- 本質像の証人は指定した頂点同型に沿って移せる。
HTT 5.5.6.28、Kerodon §4.4（Tag 01EM）、既存の同型の合成則。 -/
lemma Is0Truncated.of_vertexIso {x y : (PresheafCat C SpaceInfinity.{u}) _⦋0⦌}
    (hy : Is0Truncated y) (e : VertexIso x y) : Is0Truncated x := by
  obtain ⟨P, ⟨i⟩⟩ := hy
  exact ⟨P, ⟨e ≪≫ i⟩⟩

/-- 元の前層の押し出しの離散表示と同じ図式の任意の余極限も離散。
HTT 6.2.2.7、Kerodon 7.5.4.6（Tag 03BB）。生の頂点の等号は要求しない。 -/
lemma discretePresheafCocone_colimit_is0Truncated
    {F : AsSmall.{u} WalkingSpan ⥤ (Cᵒᵖ ⥤ Type u)}
    (c : Cocone F) (hc : IsColimit c)
    [Mono (F.map (AsSmall.up.map WalkingSpan.Hom.fst))]
    (d : JoinCocone (strictCoherentDiagram (F ⋙ kanDiscretePresheafFunctor C) ≫
      kanDiagramRealization Cᵒᵖ)) (hd : IsColimitCone d) : Is0Truncated d.vertex := by
  have hzero : Is0Truncated (discretePresheafCocone c).vertex := by
    rw [discretePresheafCocone_vertex]
    exact is0Truncated_discretePresheaf c.pt
  exact hzero.of_vertexIso (colimitVertexIso d (discretePresheafCocone c) hd
    (discretePresheafCocone_isColimit_of_span_mono c hc))

end SerrePositivity.InfinityCategories.Sheaves
