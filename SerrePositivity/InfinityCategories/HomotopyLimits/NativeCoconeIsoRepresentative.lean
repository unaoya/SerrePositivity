module

public import SerrePositivity.InfinityCategories.HomotopyLimits.NativeCoconeFamilyEvaluation
public import SerrePositivity.InfinityCategories.Core.InitialUniqueness

/-!
概要：同じ元の coslice 内の余錐同型の順方向を、全余錐と頂点で共有する可逆辺にする。
方針：ホモトピー圏への全射から元の同型を表す一つの代表を取る。
規約：元の同型の順方向の射と同じ代表を保持する。
使われ方：各評価余極限余錐の一意比較を、元の単位の可換式へ入力する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.HomotopyLimits
variable {K X : SSet.{u}} [Quasicategory X] {p : K ⟶ X} {q d : JoinCocone p}
  (e : VertexIso (X := sliceUnder p) q d)

/-- 元の余錐同型の順方向を表す、全余錐と頂点で共有する一つの代表辺。 -/
def nativeCoconeIsoRepresentative :
    SSet.Truncated.Edge (X := (truncation 2).obj (sliceUnder p)) q d :=
  Classical.choose (homotopyCategory_homMk_surjective (X := sliceUnder p) q d e.hom)

/-- 同じ元の代表辺の類は、元の余錐同型の順方向の射そのもの。 -/
lemma nativeCoconeIsoRepresentative_homMk :
    SSet.Truncated.HomotopyCategory.homMk (nativeCoconeIsoRepresentative e) = e.hom :=
  Classical.choose_spec (homotopyCategory_homMk_surjective (X := sliceUnder p) q d e.hom)

/-- 同じ元の代表辺は、元の余錐同型を表すので可逆。 -/
lemma nativeCoconeIsoRepresentative_isInvertible :
    IsInvertibleEdge (X := sliceUnder p) (nativeCoconeIsoRepresentative e) := by
  change IsIso (SSet.Truncated.HomotopyCategory.homMk (nativeCoconeIsoRepresentative e))
  rw [nativeCoconeIsoRepresentative_homMk]
  infer_instance

end SerrePositivity.InfinityCategories.HomotopyLimits
