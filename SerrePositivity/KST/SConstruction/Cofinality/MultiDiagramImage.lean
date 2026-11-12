module
public import SerrePositivity.KST.SConstruction.Cofinality.DiagramImage

/-!
概要：独立な全多次数の反復 S 図式について、本質像内の全評価から元の始域へ戻す。
方針：外側 Ar 図式を一方向ずつ戻し、最後に任意のパラメータ族を全関手同型で回収する。
規約：各反復数・多次数・元の完全射を保持し、実現後の同値性は主張しない。
使われ方：補対象を加えた有限反復 S 図式の同時回収。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：反復 S 頂点の全ての入れ子評価が指定射の本質像に属する条件。
方針：反復零では元の像条件とし、後続では全 Ar 頂点で内側の同じ条件を課す。
規約：独立な全多次数を扱い、対角へ制限しない。
使われ方：元の完全射についての有限反復図式の回収条件。 -/
def MultiPointwiseImage {X Y : StableModel.{u}} (f : X ⟶ Y) (r : ℕ) :
    (d : Fin r → SimplexCategoryᵒᵖ) →
      (((((multiSEndofunctor r).obj d).obj Y).carrier) _⦋0⦌) → Prop := by
  induction r with
  | zero => exact fun _ y => ∃ x, Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (f.val.app (Opposite.op ⦋0⦌) x) y)
  | succ r ih =>
    intro d y
    exact ∀ a : (arNerve (d 0).unop.len) _⦋0⦌,
      ih (fun i => d i.succ) ((gappedDiagram y).app (Opposite.op ⦋0⦌) a)

/-- 概要：全ての入れ子評価の本質像条件から元の反復 S 射の像に頂点を戻す。
方針：一方向の S_n 回収を反復数について帰納する。
規約：像の比較は同じ反復 S 内の頂点同型。
使われ方：全族の図式持ち上げに必要な本質像条件の証明。 -/
lemma exists_multiSVertexIso_of_pointwise_image (r : ℕ)
    (d : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}}
    (f : X ⟶ Y) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful f.val)
    (y : ((((multiSEndofunctor r).obj d).obj Y).carrier) _⦋0⦌)
    (hy : MultiPointwiseImage f r d y) :
    ∃ x : ((((multiSEndofunctor r).obj d).obj X).carrier) _⦋0⦌,
      Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((((multiSEndofunctor r).obj d).map f).val.app
        (Opposite.op ⦋0⦌) x) y) := by
  induction r generalizing X Y with
  | zero => exact hy
  | succ r ih =>
    change ∀ a : (arNerve (d 0).unop.len) _⦋0⦌,
      MultiPointwiseImage f r (fun i => d i.succ)
        ((gappedDiagram y).app (Opposite.op ⦋0⦌) a) at hy
    exact exists_sVertexIso_of_pointwise_image
      (((multiSEndofunctor r).obj (fun i => d i.succ)).map f)
      (multiSEndofunctor_map_isFullyFaithful r _ f hf) y
      (fun a => ih (fun i => d i.succ) f hf _ (hy a))

/-- 概要：本質像内の全評価を持つ反復 S 図式の任意のパラメータ族を始域へ戻す。
方針：反復 S 射の充満忠実性と頂点の像条件を全図式持ち上げへ渡す。
規約：始域パラメータは任意の単体集合で、全比較は一つの関手同型。
使われ方：有限反復図式の補対象の回収を元の S• 比較へ接続する。 -/
lemma exists_multiSFamily_of_pointwise_image (r : ℕ)
    (d : Fin r → SimplexCategoryᵒᵖ) {K : SSet.{u}} {X Y : StableModel.{u}}
    (f : X ⟶ Y) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful f.val)
    (F : K ⟶ (((multiSEndofunctor r).obj d).obj Y).carrier)
    (hF : ∀ k : K _⦋0⦌, MultiPointwiseImage f r d (F.app (Opposite.op ⦋0⦌) k)) :
    ∃ G : K ⟶ (((multiSEndofunctor r).obj d).obj X).carrier,
      Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (G ≫ (((multiSEndofunctor r).obj d).map f).val) F) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.exists_diagram_in_fullyFaithful_source _
    (multiSEndofunctor_map_isFullyFaithful r d f hf) F
    (fun k => exists_multiSVertexIso_of_pointwise_image r d f hf _ (hF k))

end SerrePositivity.KST.SConstruction.Cofinality
