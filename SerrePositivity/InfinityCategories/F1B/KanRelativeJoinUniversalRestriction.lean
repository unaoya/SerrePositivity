module

public import SerrePositivity.InfinityCategories.F1B.KanRelativeJoinFunctorMappingSpace
public import SerrePositivity.InfinityCategories.F1B.FullSubcomplexMapping
public import SerrePositivity.InfinityCategories.F1B.KanGlobalColimitFiberAssembly
public import SerrePositivity.InfinityCategories.Core.FullyFaithfulBoundary

/-!
概要：fiber ごとに普遍な相対 join 図式の全部分 ∞ 圏から元の図式への制限。
方針：通常の制限の写像空間の同値を全部分圏へ制限し、局所余極限の存在で頂点を持ち上げる。
規約：充満忠実性には余極限の存在を仮定しない。
使われ方：Kan 拡張の図式の ∞ 圏としての普遍性と coherent な選択。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：関手の頂点が全ての fiber で普遍な余錐を与える条件。
方針：関手頂点を実際の図式に戻して fiber の余錐を評価する。
規約：相対 join の右端を固定しない。
使われ方：普遍な相対 join 図式の全部分圏の頂点条件。 -/
def KanRelativeJoinColimitVertex {K C : SSet.{u}} (p : K ⟶ C) (D : SSet.{u})
    (x : ((ihom (relativeJoin p (𝟙 C))).obj D) _⦋0⦌) : Prop :=
  ∀ c : C _⦋0⦌, IsColimitCone (kanRelativeJoinFiberCocone p c
    ((functorVertexEquiv (relativeJoin p (𝟙 C)) D).symm x))

/-- 概要：全ての fiber で普遍な相対 join 図式が張る全部分単体集合。
方針：関手単体集合の頂点条件で全部分複体を作る。
規約：余極限の存在を定義に仮定しない。
使われ方：普遍図式の ∞ 圏としての制限の始域。 -/
def kanRelativeJoinColimitDiagrams {K C : SSet.{u}} (p : K ⟶ C) (D : SSet.{u}) :
    ((ihom (relativeJoin p (𝟙 C))).obj D).Subcomplex :=
  fullSubcomplexOnVertices _ (KanRelativeJoinColimitVertex p D)

/-- 概要：普遍な相対 join 図式を左端の元の図式へ制限する。
方針：全部分複体の包含の後に通常の関手の制限を合成する。
規約：元の射 p は任意。
使われ方：局所余極限から得る図式の coherent な選択の射。 -/
def kanRelativeJoinColimitRestriction {K C : SSet.{u}} (p : K ⟶ C) (D : SSet.{u}) :
    (kanRelativeJoinColimitDiagrams p D : SSet.{u}) ⟶ (ihom K).obj D :=
  (kanRelativeJoinColimitDiagrams p D).ι ≫ (pre (relativeJoinInl p (𝟙 C))).app D

/-- 概要：普遍な相対 join 図式の制限は inner fibration。
方針：全部分複体の包含と単射による通常の関手の制限の内ホーン充填を合成する。
規約：D の quasicategory 性のみを要求する。
使われ方：写像空間の充満忠実性と頂点の全射性から全境界充填へ進む。 -/
instance kanRelativeJoinColimitRestriction_innerFibration {K C D : SSet.{u}}
    [Quasicategory D] (p : K ⟶ C) : InnerFibration (kanRelativeJoinColimitRestriction p D) := by
  have : InnerFibration (kanRelativeJoinColimitDiagrams p D).ι :=
    inferInstanceAs (InnerFibration
      (fullSubcomplexOnVertices _ (KanRelativeJoinColimitVertex p D)).ι)
  exact ⟨innerFibrations.comp_mem _ _ (InnerFibration.mem (q :=
    (kanRelativeJoinColimitDiagrams p D).ι))
      (InnerFibration.mem (q := (pre (relativeJoinInl p (𝟙 C))).app D))⟩

/-- 概要：普遍な相対 join 図式の制限は写像空間の意味で充満忠実。
方針：各始点の局所余極限から制限の写像空間の同値を得て、全部分圏の包含の同値と合成する。
規約：相手の図式も含め、余極限の存在を追加仮定しない。
使われ方：Kan 図式の ∞ 圏としての普遍性。 -/
lemma kanRelativeJoinColimitRestriction_isFullyFaithful {K C D : SSet.{u}}
    [Quasicategory C] [Quasicategory D] (p : K ⟶ C) [CocartesianFibration p] :
    IsFullyFaithful (kanRelativeJoinColimitRestriction p D) := by
  intro x y
  have hx := fullSubcomplexOnVertices_vertex x
  change KanRelativeJoinColimitVertex p D x.val at hx
  let H := (functorVertexEquiv (relativeJoin p (𝟙 C)) D).symm x.val
  have hH : functorVertex H = x.val := (functorVertexEquiv _ D).apply_symm_apply _
  have hinit : InitialBoundaryLifting ((pre (relativeJoinInl p (𝟙 C))).app D) x.val := by
    rw [← hH]
    exact kanRelativeJoinFunctor_initialBoundary_of_colimit_fibers p H hx
  change IsSimplicialHomotopyEquivalence (pinchedHomMap
    ((kanRelativeJoinColimitDiagrams p D).ι ≫ (pre (relativeJoinInl p (𝟙 C))).app D) x y)
  rw [pinchedHomMap_comp]
  exact (isFullyFaithful_fullSubcomplexOnVertices_ι _ _ x y).comp
    (kanPinchedHomMap_equivalence_of_initialBoundary _ x.val y.val hinit)

/-- 概要：各元の図式に必要な局所余極限があれば普遍図式の制限は頂点で全射。
方針：局所余極限から実際の相対 join 図式を構成して全部分圏へ含める。
規約：全ての元の図式 F の各 fiber の余極限を要求する。
使われ方：普遍な Kan 図式全体からの射の零次元の境界充填。 -/
lemma kanRelativeJoinColimitRestriction_surjective {K C D : SSet.{u}}
    [Quasicategory C] [Quasicategory D] (p : K ⟶ C) [CocartesianFibration p]
    (hcol : ∀ (F : K ⟶ D) (c : C _⦋0⦌), HasColimit (vertexFiberι p c ≫ F)) :
    Function.Surjective ((kanRelativeJoinColimitRestriction p D).app (Opposite.op ⦋0⦌)) := by
  intro y
  obtain ⟨F, rfl⟩ := (functorVertexEquiv K D).surjective y
  obtain ⟨H, hH, hHi⟩ := exists_kanGlobalColimit_diagram_with_colimit_fibers p F (hcol F)
  have hv : KanRelativeJoinColimitVertex p D (functorVertex H) := by
    intro c
    have hHv : (functorVertexEquiv (relativeJoin p (𝟙 C)) D).symm (functorVertex H) = H :=
      (functorVertexEquiv _ D).symm_apply_apply H
    rw [hHv]
    exact hHi c
  let x : (kanRelativeJoinColimitDiagrams p D : SSet.{u}) _⦋0⦌ := ⟨functorVertex H, by
    intro α
    have hα : α = 𝟙 _ := Subsingleton.elim _ _
    simpa only [hα, op_id, Functor.map_id_apply] using hv⟩
  refine ⟨x, ?_⟩
  change functorVertex (relativeJoinInl p (𝟙 C) ≫ H) = functorVertex F
  rw [hH]

/-- 概要：各元の図式に必要な局所余極限があれば普遍図式の制限は自明 Kan fibration。
方針：写像空間の充満忠実性、内ホーン充填、頂点の全射性を全境界充填へ合わせる。
規約：単なる本質的全射性でなく厳密な図式の延長から頂点を持ち上げる。
使われ方：普遍図式の coherent な選択とその可縮な一意性。 -/
lemma kanRelativeJoinColimitRestriction_trivialKanFibration {K C D : SSet.{u}}
    [Quasicategory C] [Quasicategory D] (p : K ⟶ C) [CocartesianFibration p]
    (hcol : ∀ (F : K ⟶ D) (c : C _⦋0⦌), HasColimit (vertexFiberι p c ≫ F)) :
    TrivialKanFibration (kanRelativeJoinColimitRestriction p D) := by
  have : Quasicategory (kanRelativeJoinColimitDiagrams p D : SSet.{u}) :=
    inferInstanceAs (Quasicategory (fullSubcomplexOnVertices _ (KanRelativeJoinColimitVertex p D)))
  exact (kanRelativeJoinColimitRestriction_isFullyFaithful p).trivialKanFibration_of_surjective
    (kanRelativeJoinColimitRestriction_surjective p hcol)

end SerrePositivity.InfinityCategories.F1B
