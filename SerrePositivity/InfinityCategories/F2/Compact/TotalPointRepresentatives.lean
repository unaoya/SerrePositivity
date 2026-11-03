module

public import SerrePositivity.InfinityCategories.F2.Compact.WeakComponents
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.CoherentTotalObject
public import SerrePositivity.InfinityCategories.F1.Filtered.CoherentFilteredTotalDetection

/-!
概要：元の全空間 Kan 模型の点を、元の一つの図式の値の点で連結成分まで回収する。
方針：同じ Kan 置換単位の π₀ 全射性と、元の小さい fiber の値との実同値を使う。
規約：底の filtered 性・quasicategory 性は不要。元の同じ値からの比較射を保持する。
使われ方：compact 対象の恒等射を、元の表現可能生成表示の一項へ因子化する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Compact

/-- 元の全空間の Kan 模型の任意の点は、同じ図式の一つの値から成分まで回収できる。 -/
lemma coherentTotalKan_point_representative {B : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    (x : coherentDiagramTotalKan F _⦋0⦌) :
    ∃ b : B _⦋0⦌,
      ∃ v : (spaceInfinityObject (F.app (Opposite.op ⦋0⦌) (ULift.up b))).obj _⦋0⦌,
        SSet.π₀.mk ((coherentDiagramValueToTotalKan F b).app (Opposite.op ⦋0⦌) v) =
          SSet.π₀.mk x := by
  let E := smallLeftUnstraightening F
  let p := smallLeftUnstraighteningProjection F
  let η := continuousKanReplacementUnit.app E
  obtain ⟨z, hz⟩ := weakHomotopyEquivalence_mapPiZero_surjective η
    (continuousKanReplacementUnit_isWeakHomotopyEquivalence E) (SSet.π₀.mk x)
  obtain ⟨e, rfl⟩ := SSet.π₀.mk_surjective z
  rw [SSet.mapπ₀_mk] at hz
  let b := p.app (Opposite.op ⦋0⦌) e
  let v : vertexFiber p b _⦋0⦌ := ⟨e, by rw [pinchedConstant_zero]⟩
  let q := smallLeftUnstraighteningFiberValueEquivalence F b
  let w := q.hom.app (Opposite.op ⦋0⦌) v
  have H := functorHomotopyPostcomp q.homInvIso.simplicialHomotopy
    (vertexFiberι p b ≫ η)
  have h := SSet.π₀.sound (simplicialHomotopyVertexEdge H v)
  change SSet.π₀.mk ((coherentDiagramValueToTotalKan F b).app (Opposite.op ⦋0⦌) w) =
    SSet.π₀.mk (η.app (Opposite.op ⦋0⦌) e) at h
  exact ⟨b, w, h.trans hz⟩

end SerrePositivity.InfinityCategories.F2.Compact
