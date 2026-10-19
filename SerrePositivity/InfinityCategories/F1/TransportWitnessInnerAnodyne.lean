module

public import SerrePositivity.InfinityCategories.F1.TransportWitnessRestrictionLifting
public import SerrePositivity.InfinityCategories.F1.LeftFibrationInnerAnodynePullback
public import SerrePositivity.InfinityCategories.F1.InnerAnodyneReplacement

/-!
概要：inner anodyne な底の制限は表現空間の trivial Kan fibration。
方針：逆像の前合成同値、全頂点の被覆、四角形の持ち上げを組み合わせる。
規約：モデル構造の instance 仮定は使わない。
使われ方：Kerodon Lemma 5.6.8.10 (2)、表現の境界固定延長。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：inner anodyne 射は全ての頂点を被覆する。
方針：像の頂点が張る全部分複体の inner fibration に対して恒等射を持ち上げる。
規約：始域も終域も quasicategory でなくてよい。
使われ方：inner anodyne 制限から表現条件を反映する。 -/
lemma innerAnodyne_vertex_surjective {A B : SSet.{u}} (g : A ⟶ B)
    (hg : innerAnodyneExtensions g) : Function.Surjective (g.app (Opposite.op ⦋0⦌)) := by
  let P : B _⦋0⦌ → Prop := Set.range (g.app (Opposite.op ⦋0⦌))
  let a := fullSubcomplexLift P g (fun x ↦ ⟨x, rfl⟩)
  let q := (fullSubcomplexOnVertices B P).ι
  have : HasLiftingProperty g q := hg q (InnerFibration.mem (q := q))
  let sq : CommSq a g q (𝟙 B) := ⟨by
    rw [Category.comp_id]
    exact fullSubcomplexLift_ι _ _ _⟩
  intro b
  have hb := fullSubcomplexOnVertices_vertex (sq.lift.app (Opposite.op ⦋0⦌) b)
  have he := congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) b) sq.fac_right
  change (sq.lift.app (Opposite.op ⦋0⦌) b).val = b at he
  change P _ at hb
  rw [he] at hb
  exact hb

/-- 概要：inner anodyne な底への四角形の制限は全ての単射を持ち上げる。
方針：left fibration に沿う逆像の前合成同値を相対内部 Hom の判定に入れる。
規約：底と全空間の quasicategory 性は不要。
使われ方：Kerodon Lemma 5.6.8.10 (2)、周囲の四角形の充填。 -/
lemma transportSquareRestriction_trivialKanFibration_of_innerAnodyne
    {E B D : SSet.{u + 1}} (p : E ⟶ B) [LeftFibration p] (g : D ⟶ B)
    (hg : innerAnodyneExtensions g) : TrivialKanFibration (transportSquareRestriction p g) := by
  have : Mono g := mono_of_innerAnodyne g hg
  exact transportSquareRestriction_trivialKanFibration_of_precompositionEquivalences p g
    (isPrecompositionEquivalence_of_innerAnodyne g hg)
    (leftFibration_pullback_innerAnodyne_isPrecompositionEquivalence p g hg)

/-- 概要：inner anodyne な底への表現空間の制限は全ての単射を持ち上げる。
方針：周囲の四角形の充填を全頂点の被覆で表現空間へ制限する。
規約：存在や一意性を追加の公理として要求しない。
使われ方：Kerodon Lemma 5.6.8.10 (2) の空間値版。 -/
lemma transportWitnessRestriction_trivialKanFibration_of_innerAnodyne
    {E B D : SSet.{u + 1}} (p : E ⟶ B) [LeftFibration p] (g : D ⟶ B)
    (hg : innerAnodyneExtensions g) : TrivialKanFibration (transportWitnessRestriction p g) :=
  transportWitnessRestriction_trivialKanFibration_of_square p g
    (innerAnodyne_vertex_surjective g hg)
    (transportSquareRestriction_trivialKanFibration_of_innerAnodyne p g hg)

end SerrePositivity.InfinityCategories
