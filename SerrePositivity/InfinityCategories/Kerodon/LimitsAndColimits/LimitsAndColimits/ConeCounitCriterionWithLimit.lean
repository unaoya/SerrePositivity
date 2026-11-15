module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConeMorphismBoundary
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.RightFibrationReflection
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TerminalTransport

/-!
概要：極限が存在する図式では、指定余単位の Hom 全単射で元の錐の極限性を判定する。
方針：実際の極限錐への比較辺を取り、二つの全単射でその頂点射の逆射を作る。
使われ方：Kerodon §7.1（Tag 02H1）、HTT 6.2.2.6 の降下の合成。
規約：この中間補題は極限の存在を明示する。一般の係数で π₀ の判定を主張しない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 既存の極限への実際の比較射を、元の指定余単位の全単射で可逆にする。 -/
lemma isLimitCone_of_coneCounitHom_bijective {K X : SSet.{u}} [Quasicategory X]
    {p : K ⟶ X} (hp : HasLimit p) (c : JoinCone p)
    (hc : ∀ y : X _⦋0⦌, Function.Bijective
      (fun β : (SSet.HomotopyCategory.mk y : hoFunctor.obj X) ⟶
        SSet.HomotopyCategory.mk c.vertex => constantFunctorHomMap K β ≫ coneCounitHom c)) :
    IsLimitCone c := by
  obtain ⟨d, hd⟩ := hp
  obtain ⟨e₀⟩ := IsTerminalVertex.nonempty_edge (X := sliceOver p) hd c
  let e := SSet.Edge.ofTruncated (X := sliceOver p) e₀
  let β := SSet.HomotopyCategory.homMk e
  let g : (SSet.HomotopyCategory.mk c.vertex : hoFunctor.obj X) ⟶
      SSet.HomotopyCategory.mk d.vertex :=
    (hoFunctor.map (sliceOverProjection p)).toFunctor.map β
  have hn : constantFunctorHomMap K g ≫ coneCounitHom d = coneCounitHom c :=
    coneCounitHom_coneMorphism β
  obtain ⟨k, hk⟩ := (hc d.vertex).surjective (coneCounitHom d)
  change constantFunctorHomMap K k ≫ coneCounitHom c = coneCounitHom d at hk
  have hkg : k ≫ g = 𝟙 _ := by
    apply (coneCounitHom_bijective d hd d.vertex).injective
    simp only [constantFunctorHomMap_comp, Category.assoc]
    rw [hn, hk, constantFunctorHomMap_id, Category.id_comp]
  have hgk : g ≫ k = 𝟙 _ := by
    apply (hc c.vertex).injective
    simp only [constantFunctorHomMap_comp, Category.assoc]
    rw [hk, hn, constantFunctorHomMap_id, Category.id_comp]
  have hg : IsIso g := ⟨⟨k, hgk, hkg⟩⟩
  have ha : IsInvertibleEdge (e.map (sliceOverProjection p)).toTruncated := hg
  have hi := derived_rightFibration_reflects_invertibleEdge
    (sliceOverProjection p) e.toTruncated ha
  letI : IsIso (SSet.Truncated.HomotopyCategory.homMk e.toTruncated) := hi
  exact hd.of_vertexIso (asIso (SSet.Truncated.HomotopyCategory.homMk e.toTruncated)).symm

/-- 極限の存在を明示した場合の、同じ錐・同じ余単位による判定。 -/
lemma isLimitCone_iff_coneCounitHom_bijective_of_hasLimit
    {K X : SSet.{u}} [Quasicategory X] {p : K ⟶ X} (hp : HasLimit p) (c : JoinCone p) :
    IsLimitCone c ↔ ∀ y : X _⦋0⦌, Function.Bijective
      (fun β : (SSet.HomotopyCategory.mk y : hoFunctor.obj X) ⟶
        SSet.HomotopyCategory.mk c.vertex => constantFunctorHomMap K β ≫ coneCounitHom c) :=
  ⟨fun h y => coneCounitHom_bijective c h y,
    isLimitCone_of_coneCounitHom_bijective hp c⟩

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
