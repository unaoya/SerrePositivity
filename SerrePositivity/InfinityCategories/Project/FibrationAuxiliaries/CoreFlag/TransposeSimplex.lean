module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag.Basic
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalenceDiagrams

/-!
概要：二つの標準単体を引数とする関手族の交換。
方針：内部 Hom の単体を二変数の作用として読み、二つの変数を交換する。
規約：core の条件を移す前の全関手単体集合で構成する。
使われ方：Sp-8 の転置した行を全辺可逆な図式の部分圏と同定する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped _root_.Simplicial
namespace SerrePositivity.KST.LocalizingInvariants.CoreFlag
end SerrePositivity.KST.LocalizingInvariants.CoreFlag
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag
open _root_.SerrePositivity.KST.LocalizingInvariants.CoreFlag
open InfinityCategories

/-- 二つの標準単体の変数を交換した内部 Hom の単体。 -/
def transposeSimplex {C : SSet.{u}} {n m : SimplexCategoryᵒᵖ}
    (s : ((ihom (stdSimplex.obj n.unop)).obj C).obj m) :
    ((ihom (stdSimplex.obj m.unop)).obj C).obj n where
  app d g := ↾fun x ↦ s.app d (stdSimplex.objEquiv x).op (stdSimplex.objEquiv.symm g.unop)
  naturality {d e} f g := by
    apply ConcreteCategory.hom_ext
    intro x
    have h := ConcreteCategory.congr_hom
      (s.naturality f (stdSimplex.objEquiv x).op) (stdSimplex.objEquiv.symm g.unop)
    dsimp at h ⊢
    convert h using 1
    congr 2

/-- 変数交換を二度行うと元の単体に戻る。 -/
@[simp]
lemma transposeSimplex_transposeSimplex {C : SSet.{u}} {n m : SimplexCategoryᵒᵖ}
    (s : ((ihom (stdSimplex.obj n.unop)).obj C).obj m) :
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag.transposeSimplex (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag.transposeSimplex s) = s := by
  apply Functor.functorHom_ext
  intro d g
  apply ConcreteCategory.hom_ext
  intro x
  dsimp [_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag.transposeSimplex]
  simp only [Equiv.symm_apply_apply, Equiv.apply_symm_apply, Quiver.Hom.op_unop]

/-- 任意の内部 Hom の辺の可逆性を全頂点評価で判定する。 -/
lemma functorSimplex_isInvertible_iff {A C : SSet.{u}} [Quasicategory C]
    (e : ((ihom A).obj C) _⦋1⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex e) ↔ ∀ a : A _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := C) a).app _ e)) := by
  let f := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv A C).symm (((ihom A).obj C).δ 1 e)
  let g := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv A C).symm (((ihom A).obj C).δ 0 e)
  let e' : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom A).obj C))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex g) :=
    { edge := e
      src_eq := (Equiv.apply_symm_apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv A C) _).symm
      tgt_eq := (Equiv.apply_symm_apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv A C) _).symm }
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.isInvertibleEdge_iff_evaluateFunctorAt e'
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex e) (f := e') rfl).trans
    (h.trans (forall_congr' (fun a ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr
      (e := e'.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := C) a)))
      (f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := C) a).app _ e)) rfl)))

/-- 関手頂点の逆表示の各次数での評価。 -/
lemma functorVertexEquiv_symm_app {A C : SSet.{u}}
    (v : ((ihom A).obj C) _⦋0⦌) (d : SimplexCategoryᵒᵖ) (x : A.obj d) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv A C).symm v).app d x =
      v.app d (SimplexCategory.const d.unop ⦋0⦌ 0).op x := by
  obtain ⟨f, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv A C).surjective v
  rw [Equiv.symm_apply_apply]
  rfl

/-- 転置した図式の頂点での辺は、元の関手辺の点ごとの評価。 -/
lemma transpose_vertex_edge {C : SSet.{u}} {n m : SimplexCategoryᵒᵖ}
    (s : ((ihom (stdSimplex.obj n.unop)).obj C).obj m)
    (v : ⦋0⦌ ⟶ n.unop) (e : (stdSimplex.obj m.unop) _⦋1⦌) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (stdSimplex.obj m.unop) C).symm
      (((ihom (stdSimplex.obj m.unop)).obj C).map v.op (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag.transposeSimplex s))).app _ e =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := C) (stdSimplex.objEquiv.symm v)).app _
      (((ihom (stdSimplex.obj n.unop)).obj C).map (stdSimplex.objEquiv e).op s) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag.functorVertexEquiv_symm_app]
  change s.app (Opposite.op ⦋1⦌) (stdSimplex.objEquiv e).op
      (stdSimplex.objEquiv.symm ((SimplexCategory.const ⦋1⦌ ⦋0⦌ 0) ≫ v)) =
    s.app (Opposite.op ⦋1⦌) ((stdSimplex.objEquiv e).op ≫ 𝟙 _)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.objEquiv.symm v) 1)
  dsimp [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant]
  simp only [Category.comp_id]
  congr 1

/-- core の条件は転置後には全辺可逆な図式という頂点条件になる。 -/
lemma transpose_mem_iff {C : SSet.{u}} [Quasicategory C] {n m : SimplexCategoryᵒᵖ}
    (s : ((ihom (stdSimplex.obj n.unop)).obj C).obj m) :
    s ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore ((ihom (stdSimplex.obj n.unop)).obj C)).obj m ↔
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag.transposeSimplex s ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices
      ((ihom (stdSimplex.obj m.unop)).obj C)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsEquivalenceDiagramVertex (stdSimplex.obj m.unop) C)).obj n := by
  constructor
  · intro hs v e
    rw [_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag.transpose_vertex_edge]
    have h := hs (stdSimplex.objEquiv e)
    exact (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag.functorSimplex_isInvertible_iff _).mp h (stdSimplex.objEquiv.symm v)
  · intro hs f
    apply (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag.functorSimplex_isInvertible_iff _).mpr
    intro a
    have h := hs (stdSimplex.objEquiv a) (stdSimplex.objEquiv.symm f)
    rw [_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag.transpose_vertex_edge] at h
    have ha : stdSimplex.objEquiv.symm (stdSimplex.objEquiv a) = a :=
      stdSimplex.objEquiv.symm_apply_apply a
    have hf : stdSimplex.objEquiv.{u} (stdSimplex.objEquiv.{u}.symm f) = f :=
      stdSimplex.objEquiv.{u}.apply_symm_apply f
    rw [ha, hf] at h
    exact h

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
