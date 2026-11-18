module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.EmptyCone
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.FunctorVertexConeReindex

/-!
概要：任意の空形状の指定錐の極限性を、その同じ頂点の終対象性で判定する。
方針：初期単体集合の一意同型で標準の空部分複体へ制限し、元の頂点射影を使う。
使われ方：HTT §1.2.12、Kerodon §7.1（Tag 02H1）の空積、有限極限保存の空形状の計算。
規約：形状が空であることを実際の初期対象性として明示し、頂点を変えない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
open SerrePositivity.InfinityCategories.Project.FilteredExchange
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits

/-- 空形状の元の指定極限錐は、同じ頂点の終対象性で判定できる。 -/
lemma isLimitCone_iff_terminal_of_initialShape {K X : SSet.{u}}
    (hK : Limits.IsInitial K) {p : K ⟶ X} (c : JoinCone p) :
    IsLimitCone c ↔ IsTerminalVertex c.vertex := by
  let e := (Subcomplex.isInitialBot (X := X)).uniqueUpToIso hK
  have hp : e.hom ≫ p = (⊥ : X.Subcomplex).ι := Subcomplex.isInitialBot.hom_ext _ _
  let r := restrictJoinCone c e.hom
  let d : JoinCone (⊥ : X.Subcomplex).ι := ⟨r.val, r.property.trans hp⟩
  have hv : d.vertex = c.vertex := restrictJoinCone_vertex c e.hom
  have hd : IsLimitCone d ↔ IsTerminalVertex d.vertex := by
    constructor
    · intro h
      exact h.map_of_isIso (sliceOverProjection (⊥ : X.Subcomplex).ι)
    · intro h
      exact isTerminalVertex_of_trivialKanFibration
        (sliceOverProjection (⊥ : X.Subcomplex).ι) h
  calc
    IsLimitCone c ↔ IsLimitCone r := (isLimitCone_restrict_iff_of_isIso c e.hom).symm
    _ ↔ IsLimitCone d := isLimitCone_iff_of_diagram_eq hp rfl
    _ ↔ IsTerminalVertex d.vertex := hd
    _ ↔ IsTerminalVertex c.vertex := by rw [hv]

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
