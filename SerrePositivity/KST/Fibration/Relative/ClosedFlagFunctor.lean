module
public import SerrePositivity.KST.Fibration.Relative.ClosedStableFlags
public import SerrePositivity.KST.Fibration.WeakStringRealizationConstants
public import SerrePositivity.KST.SConstruction.ClosedSubcategoryFunctor

/-!
概要：商を使わない相対旗の全単体的構造。
方針：全体持ち上げ条件を制限し、既存の完全な全部分圏写像を使う。
規約：選んだ cofiber の厳密自然性は要求せず、全辺条件で自然性を証明する。
使われ方：元の R_P と core S 実現の単体的図式。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Fibration.Relative

/-- 概要：元の旗の面・退化による完全な制限。
方針：全辺条件を使う。規約：全ての単体作用素。使われ方：R_P の射作用。 -/
def closedFlagMap {B : StableModel.{u}} (P : ClosedStablePredicate B)
    {m n : SimplexCategory} (θ : m ⟶ n) : closedFlagModel P n ⟶ closedFlagModel P m :=
  closedStableMap (closedFlagStablePredicate P n) (closedFlagStablePredicate P m)
    (diagramRestrictionMap (flagAmbient B) θ) (by
      intro v hv
      apply (closedFlagStablePredicate_iff P m _).2
      unfold closedFlagPredicate
      change simplexVertexValue m
        (((pre (stdSimplex.map θ)).app B.carrier).app (Opposite.op ⦋0⦌) v) ∈ _
      rw [simplexVertexValue_reindex]
      exact (edgewiseSubcomplex (closedStableEdges P)).map θ.op
        ((closedFlagStablePredicate_iff P n v).1 hv))

/-- 概要：旗制限の周囲への包含。方針：既存の完全制限公式。
規約：元の前合成と一致。使われ方：全高次単体の照合。 -/
lemma closedFlagMap_inclusion {B : StableModel.{u}} (P : ClosedStablePredicate B)
    {m n : SimplexCategory} (θ : m ⟶ n) :
    closedFlagMap P θ ≫ closedStableInclusion (closedFlagStablePredicate P m) =
      closedStableInclusion (closedFlagStablePredicate P n) ≫
        diagramRestrictionMap (flagAmbient B) θ :=
  closedStableMap_inclusion _ _ _ _

/-- 概要：R_P の全単体的な安定模型。方針：包含の単射性で関手則を検証する。
規約：全自然変換を保つ。使われ方：core S を適用する元の図式。 -/
def closedFlagSimplicial {B : StableModel.{u}} (P : ClosedStablePredicate B) :
    SimplicialObject StableModel.{u} where
  obj n := closedFlagModel P n.unop
  map θ := closedFlagMap P θ.unop
  map_id n := by
    apply closedStableInclusion_cancel (closedFlagStablePredicate P n.unop)
    rw [closedFlagMap_inclusion, Category.id_comp]
    apply Subtype.ext
    change (closedStableInclusion (closedFlagStablePredicate P n.unop)).val ≫
      (pre (stdSimplex.map (𝟙 n).unop)).app B.carrier = _
    rw [unop_id, CategoryTheory.Functor.map_id, pre_id, NatTrans.id_app]
    exact Category.comp_id _
  map_comp {n m k} θ φ := by
    apply closedStableInclusion_cancel (closedFlagStablePredicate P _)
    rw [closedFlagMap_inclusion, Category.assoc, closedFlagMap_inclusion,
      ← Category.assoc, closedFlagMap_inclusion, Category.assoc]
    apply Subtype.ext
    change (closedStableInclusion (closedFlagStablePredicate P n.unop)).val ≫
      (pre (stdSimplex.map (θ ≫ φ).unop)).app B.carrier =
        (closedStableInclusion (closedFlagStablePredicate P n.unop)).val ≫
          ((pre (stdSimplex.map θ.unop)).app B.carrier ≫
            (pre (stdSimplex.map φ.unop)).app B.carrier)
    simp only [unop_comp, stdSimplex.map_comp, pre_map, NatTrans.comp_app]

/-- 概要：全旗の元の core S 実現を全単体的に保持。
方針：K-S• の実現関手で後合成。規約：F は単回版。使われ方：相対実現の底。 -/
def closedFlagRealizationDiagram {B : StableModel.{u}} (P : ClosedStablePredicate B) :
    SimplicialObject SSet.{u} := closedFlagSimplicial P ⋙ coreSRealizationFunctor

/-- 概要：全旗・S・内部単体方向の同時実現。
方針：元の二重単体集合の対角。規約：局所化圏値図式は使用しない。
使われ方：c_B の元の標的。 -/
def closedRelativeRealization {B : StableModel.{u}} (P : ClosedStablePredicate B) : SSet.{u} :=
  simplicialDiagonalFunctor.obj (closedFlagRealizationDiagram P)

/-- 概要：指定頂点の完全な評価。方針：全部分旗の包含と周囲の評価を合成。
規約：元の B への射。使われ方：定数旗と第一頂点の比較。 -/
def closedFlagVertex {B : StableModel.{u}} (P : ClosedStablePredicate B)
    (n : SimplexCategory) (j : Fin (n.len + 1)) : closedFlagModel P n ⟶ B :=
  closedStableInclusion (closedFlagStablePredicate P n) ≫
    ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm j),
      (evaluateFunctorAt_preservesSConstructionData _).toCofiberData⟩

/-- 概要：元の頂点評価と全再添字の厳密可換性。
方針：周囲への包含で計算。規約：全頂点。使われ方：初期評価の単体的比較。 -/
lemma closedFlagVertex_reindex {B : StableModel.{u}} (P : ClosedStablePredicate B)
    {m n : SimplexCategory} (θ : m ⟶ n) (j : Fin (m.len + 1)) :
    closedFlagMap P θ ≫ closedFlagVertex P m j =
      closedFlagVertex P n (θ.toOrderHom j) := by
  unfold closedFlagVertex
  rw [← Category.assoc, closedFlagMap_inclusion, Category.assoc]
  apply Subtype.ext
  change ((closedStableInclusion (closedFlagStablePredicate P n)).val ≫
    (pre (stdSimplex.map θ)).app B.carrier) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm j) = _
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.stable_pre_evaluateFunctorAt]
  rfl

end SerrePositivity.KST.Fibration.Relative
